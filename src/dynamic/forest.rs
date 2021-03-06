//! Forest.

mod chain_builder;
mod debug_print;
mod nest_builder;
mod node;
pub(crate) mod traverse;

use core::fmt;

use alloc::vec::Vec;

use crate::dynamic::hierarchy::traverse::{
    DepthFirstTraverser, DftEvent, SafeModeDepthFirstTraverser,
};
use crate::dynamic::hierarchy::{Hierarchy, Neighbors};
use crate::dynamic::{InsertAs, InternalNodeId, NodeId, NodeIdExt};

pub use self::chain_builder::ChainTreeBuilder;
pub use self::debug_print::DebugPrint;
pub use self::nest_builder::NestTreeBuilder;
pub use self::node::{Node, NodeMut};

/// Forest.
///
/// Forest is a set of trees.
/// This type does not remember root nodes, so users are responsible to remember
/// root nodes they created.
///
/// # Usage
///
/// ## Forest creation
///
/// Forest can be created by [`Forest::new`] method.
///
/// ```
/// use treena::dynamic::{Forest, NodeIdUsize};
///
/// // Usually you want the forest to be `mut` to modify structure.
/// let forest = Forest::<NodeIdUsize, i64>::new();
/// ```
///
/// ## Building tree and modifying structure
///
/// There are some ways to construct a tree and/or rebuild trees.
///
/// **[`ChainTreeBuilder`]** let you create a new root node and its descendants
/// at once. For detail, see the documentation for [`ChainTreeBuilder`].
///
/// **[`Forest::create_root`]** method let you create a new root node.
/// Note that a forest can have multiple root nodes.
///
/// **[`Forest::create_insert`]** method let you create a new node and insert
/// it immediately to some place.
///
/// **[`Forest::detach`]** method let you detach a subtree from parent and
/// siblings. The detached node becomes a new root node.
///
/// Nodes in the forest can be adopted (transplanted) to another place.
/// **[`Forest::insert`]** method let you detach some subtree and insert it to
/// the specified place.
///
/// **[`Forest::detach_single`]** method let pyou detach a single node from
/// all neighbors including children. The detached node becomes a new root node.
/// Children of the detached node will be expanded to the place where the
/// detached node was.
/// For detail, see the method documentation.
///
/// **[`Forest::remove`]**, **[`Forest::remove_hooked`]**, and
/// **[`Forest::remove_hooked_panic_safe`]** let you remove the subtree from
/// the forest. Data associated to the nodes are passed to the given function
/// in "hooked" variants. If you don't need associated data, you can just use
/// [`Forest::remove`].
///
/// **[`Forest::clone_local_tree`]** and **[`Forest::clone_foreign_tree`]**
/// clones a subtree into a forest (by deep-copy). Local version clones the tree
/// inside the same forest, and foreign version clones the tree from a forest
/// into another forest.
///
/// ## Neighbors access
///
/// You need to use [`Node`] proxy object to get neighbors.
/// See the documentation for [`Node`] type.
///
/// ## Traversal and iterators
///
/// **[`Forest::ancestors`]** and **[`Forest::ancestors_or_self`]** method
/// returns an iterator of ancestors.
///
/// **[`Forest::children`]** method returns an iterator of children.
///
/// **[`Forest::following_siblings`]** and
/// **[`Forest::following_siblings_or_self`]** methods return iterators of
/// following siblings.
///
/// **[`Forest::preceding_siblings`]** and
/// **[`Forest::preceding_siblings_or_self`]** methods return iterators of
/// preceding siblings.
/// Note that the order of iteration is first to last. If you want to iterate
/// from current node to the first sibling, use `Iterator::rev()` to the
/// iterator.
///
/// **[`Forest::depth_first_traverse`]** method let you iterate the tree by
/// depth-first traversal.
///
/// **[`Forest::shallow_depth_first_traverse`]** method also let you iterate
/// the tree by depth-first traversal, but with limited depth.
/// Nodes deeper than the given limit are efficiently skipped.
///
/// **[`Forest::breadth_first_traverse`]** and
/// **[`Forest::allocating_breadth_first_traverse`]** method let you iterate the
/// tree by breadth-first traversal.
/// Note that the iterator returned by [`Forest::breadth_first_traverse`] method
/// does not heap-allocate, but iterating all nodes will be `O(n^2)` operation
/// in worst case, not `O(n)`.
#[derive(Debug, Clone)]
pub struct Forest<Id: NodeId, T> {
    /// Hierarchy.
    hierarchy: Hierarchy<Id::Internal>,
    /// Data.
    ///
    /// `None` is used for removed nodes.
    // This can be `Vec<MaybeUninit<T>>` since `self.hierarchy` knows which
    // nodes are removed. However, manually managing possibly uninitialized
    // elements would be error prone and unsafe. To avoid bugs from `unsafe`
    // codes, use `Option<T>` here.
    data: Vec<Option<T>>,
}

/// Forest creation.
impl<Id: NodeId, T> Forest<Id, T> {
    /// Creates a new empty forest.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    ///
    /// let id = forest.create_root(42);
    /// assert_eq!(forest.data(id).copied(), Some(42));
    /// ```
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

/// Individual node access.
impl<Id: NodeId, T> Forest<Id, T> {
    /// Returns true if the node exists and is not yet removed.
    #[must_use]
    fn is_alive(&self, id: Id) -> bool {
        self.data
            .get(id.to_usize())
            .map_or(false, |entry| entry.is_some())
    }

    /// Returns a [proxy object][`Node`] to the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let id = forest.create_root(42);
    ///
    /// let node = forest.node(id).expect("should never fail: node exists");
    ///
    /// // Can access the associated data.
    /// assert_eq!(*node.data(), 42);
    /// // Can access the neighbors data.
    /// assert!(
    ///     node.parent_id().is_none(),
    ///     "the root node does not have a parent"
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn node(&self, id: Id) -> Option<Node<'_, Id, T>> {
        Node::new(self, id)
    }

    /// Returns a [proxy object][`NodeMut`] to the mutable node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{AdoptAs, Forest, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let id = forest.create_root(42);
    ///
    /// let mut node = forest.node_mut(id).expect("should never fail: node exists");
    ///
    /// // Can access the associated data.
    /// assert_eq!(*node.data(), 42);
    /// // Can modify the associated data.
    /// *node.data_mut() = 314;
    /// assert_eq!(*node.data(), 314);
    ///
    /// // Can create nodes as neighbors.
    /// node.create(141421356, AdoptAs::LastChild);
    ///
    /// let node = forest.node(id).expect("should never fail: node exists");
    /// assert_eq!(
    ///     node
    ///         .children()
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &[141421356]
    /// )
    /// ```
    #[inline]
    #[must_use]
    pub fn node_mut(&mut self, id: Id) -> Option<NodeMut<'_, Id, T>> {
        NodeMut::new(self, id)
    }

    /// Returns a reference to the data associated to the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let id = forest.create_root(42);
    ///
    /// assert_eq!(forest.data(id).copied(), Some(42));
    /// ```
    #[inline]
    #[must_use]
    pub fn data(&self, id: Id) -> Option<&T> {
        self.data
            .get(id.to_usize())
            .and_then(|entry| entry.as_ref())
    }

    /// Returns a reference to the data associated to the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let id = forest.create_root(42);
    /// assert_eq!(forest.data(id).copied(), Some(42));
    ///
    /// *forest.data_mut(id).expect("should never fail: node exists") = 314;
    ///
    /// assert_eq!(forest.data(id).copied(), Some(314));
    /// ```
    #[inline]
    #[must_use]
    pub fn data_mut(&mut self, id: Id) -> Option<&mut T> {
        self.data
            .get_mut(id.to_usize())
            .and_then(|entry| entry.as_mut())
    }

    /// Returns a reference to the neighbors data associated to the node.
    #[inline]
    #[must_use]
    fn neighbors(&self, id: Id) -> Option<&Neighbors<Id::Internal>> {
        self.hierarchy.neighbors(id.to_internal())
    }
}

/// Node creation and/or insertion.
impl<Id: NodeId, T> Forest<Id, T> {
    /// Creates a new root node.
    ///
    /// # Panics
    ///
    /// Panics if the node ID overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let id = forest.create_root(42);
    /// assert_eq!(forest.data(id).copied(), Some(42));
    /// assert!(
    ///     forest
    ///         .node(id)
    ///         .expect("should never fail: node exists")
    ///         .parent_id()
    ///         .is_none(),
    ///     "the root node does not have a parent"
    /// );
    /// ```
    ///
    /// The newly added root node has no connections between other trees.
    ///
    /// ```
    /// use treena::dynamic::{Forest, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let another_root = forest.create_root(42);
    ///
    /// let root = forest.create_root(314);
    ///
    /// let root_node = forest.node(root).expect("should never fail: node exists");
    /// assert_eq!(*root_node.data(), 314);
    /// assert!(
    ///     root_node.parent_id().is_none(),
    ///     "the root node does not have a parent"
    /// );
    /// assert!(
    ///     root_node.next_sibling_id().is_none(),
    ///     "the root node does not have siblings"
    /// );
    /// assert!(
    ///     root_node.prev_sibling_id().is_none(),
    ///     "the root node does not have siblings"
    /// );
    /// assert!(
    ///     root_node.first_child_id().is_none(),
    ///     "the root node does not have children"
    /// );
    /// assert!(
    ///     root_node.last_child_id().is_none(),
    ///     "the root node does not have children"
    /// );
    /// ```
    #[must_use = "newly created node cannot be accessed without the returned node ID"]
    pub fn create_root(&mut self, data: T) -> Id {
        let new_id = self.hierarchy.create_root();
        assert_eq!(
            self.data.len(),
            new_id.to_usize(),
            "[consistency] node ID must be able to be used as an index for the vec"
        );
        self.data.push(Some(data));

        Id::from_internal(new_id)
    }

    /// Creates a node and inserts it to the target position.
    ///
    /// Returns the node ID of the newly created node.
    ///
    /// To see how [`InsertAs`] works, see [`insert`][`Self::insert`] method.
    ///
    /// # Panics
    ///
    /// * Panics if the node (the anchor of the destination) is not alive.
    /// * Panics if the node (the anchor of the destination) is not from this forest.
    #[inline]
    #[must_use = "newly created node cannot be accessed without the returned node ID"]
    pub fn create_insert(&mut self, data: T, dest: InsertAs<Id>) -> Id {
        Id::from_internal(create_insert_momo(
            &mut self.hierarchy,
            &mut self.data,
            data,
            dest.map(Id::to_internal),
        ))
    }
}

/// Detaching and insertion.
impl<Id: NodeId, T> Forest<Id, T> {
    /// Detaches and inserts the given node to the target position.
    ///
    /// # Panics
    ///
    /// Panics if any of the given nodes (including the anchor of the destination)
    /// are not alive.
    ///
    /// # Errors
    ///
    /// * [`StructureError::AncestorDescendantLoop`]
    ///     + In case `dest` is `FirstChildOf(node)` or `LastChildOf(node)`.
    /// * [`StructureError::UnorderableSiblings`]
    ///     + In case `dest` is `PreviousSiblingOf(node)` or `NextSiblingOf(node)`.
    /// * [`StructureError::SiblingsWithoutParent`]
    ///     + In case `dest` is `PreviousSiblingOf(v)` or `NextSiblingOf(v)`, and
    ///       `v` does not have a parent.
    ///
    /// # Examples
    ///
    /// [`InsertAs::NextSiblingOf`] inserts the node as the next sibling of
    /// some other node.
    ///
    /// ```
    /// use treena::dynamic::InsertAs;
    ///
    /// # use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
    /// # let mut forest = Forest::<NodeIdUsize, _>::new();
    /// # let mut builder = ChainTreeBuilder::new(&mut forest, "root");
    /// # let child_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .current_id();
    /// # builder
    /// #     .child("1-0")
    /// #     .sibling("1-1")
    /// #     .sibling("1-2")
    /// #     .parent()
    /// #     .sibling("2");
    /// # let root = builder.root_id();
    /// let before = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), before);
    ///
    /// // Create a new node.
    /// let new = forest.create_root("new");
    /// // Insert the node "new" as the next sibling of the node "1".
    /// forest.insert(new, InsertAs::NextSiblingOf(child_1));
    ///
    /// let after_insert = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// |-- new
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), after_insert);
    /// ```
    ///
    /// [`InsertAs::PreviousSiblingOf`] inserts the node as the previous sibling
    /// of some other node.
    ///
    /// ```
    /// use treena::dynamic::InsertAs;
    ///
    /// # use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
    /// # let mut forest = Forest::<NodeIdUsize, _>::new();
    /// # let mut builder = ChainTreeBuilder::new(&mut forest, "root");
    /// # let child_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .current_id();
    /// # builder
    /// #     .child("1-0")
    /// #     .sibling("1-1")
    /// #     .sibling("1-2")
    /// #     .parent()
    /// #     .sibling("2");
    /// # let root = builder.root_id();
    /// let before = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), before);
    ///
    /// // Create a new node.
    /// let new = forest.create_root("new");
    /// // Insert the node "new" as the previous sibling of the node "1".
    /// forest.insert(new, InsertAs::PreviousSiblingOf(child_1));
    ///
    /// let after_insert = r#"root
    /// |-- 0
    /// |-- new
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), after_insert);
    /// ```
    ///
    /// [`InsertAs::FirstChildOf`] inserts the node as the first child of some
    /// other node.
    ///
    /// ```
    /// use treena::dynamic::InsertAs;
    ///
    /// # use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
    /// # let mut forest = Forest::<NodeIdUsize, _>::new();
    /// # let mut builder = ChainTreeBuilder::new(&mut forest, "root");
    /// # let child_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .current_id();
    /// # builder
    /// #     .child("1-0")
    /// #     .sibling("1-1")
    /// #     .sibling("1-2")
    /// #     .parent()
    /// #     .sibling("2");
    /// # let root = builder.root_id();
    /// let before = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), before);
    ///
    /// // Create a new node.
    /// let new = forest.create_root("new");
    /// // Insert the node "new" as the first child of the node "1".
    /// forest.insert(new, InsertAs::FirstChildOf(child_1));
    ///
    /// let after_insert = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- new
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), after_insert);
    /// ```
    ///
    /// [`InsertAs::LastChildOf`] inserts the node as the last child of some
    /// other node.
    ///
    /// ```
    /// use treena::dynamic::InsertAs;
    ///
    /// # use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
    /// # let mut forest = Forest::<NodeIdUsize, _>::new();
    /// # let mut builder = ChainTreeBuilder::new(&mut forest, "root");
    /// # let child_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .current_id();
    /// # builder
    /// #     .child("1-0")
    /// #     .sibling("1-1")
    /// #     .sibling("1-2")
    /// #     .parent()
    /// #     .sibling("2");
    /// # let root = builder.root_id();
    /// let before = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), before);
    ///
    /// // Create a new node.
    /// let new = forest.create_root("new");
    /// // Insert the node "new" as the last child of the node "1".
    /// forest.insert(new, InsertAs::LastChildOf(child_1));
    ///
    /// let after_insert = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   |-- 1-2
    /// |   `-- new
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), after_insert);
    /// ```
    #[inline]
    pub fn insert(&mut self, node: Id, dest: InsertAs<Id>) -> Result<(), StructureError> {
        self.hierarchy
            .insert(node.to_internal(), dest.map(Id::to_internal))
    }
}

/// Detaching and/or removal.
impl<Id: NodeId, T> Forest<Id, T> {
    /// Detaches the tree from neighbors.
    ///
    /// Tree structure under the given node will be preserved.
    /// The detached node will become a root node.
    ///
    /// If you want to detach not subtree but single node, use
    /// [`detach_single`][`Self::detach_single`] method.
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
    ///
    /// # Examples
    ///
    /// ```
    /// # use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
    /// # let mut forest = Forest::<NodeIdUsize, _>::new();
    /// # let mut builder = ChainTreeBuilder::new(&mut forest, "root");
    /// # let child_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .current_id();
    /// # builder
    /// #     .child("1-0")
    /// #     .sibling("1-1")
    /// #     .sibling("1-2")
    /// #     .parent()
    /// #     .sibling("2");
    /// # let root = builder.root_id();
    /// let before = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), before);
    ///
    /// // Detach the node "1".
    /// forest.detach(child_1);
    ///
    /// let after_detach_root = r#"root
    /// |-- 0
    /// `-- 2"#;
    /// let after_detach_child_1 = r#"1
    /// |-- 1-0
    /// |-- 1-1
    /// `-- 1-2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), after_detach_root);
    /// assert_eq!(forest.debug_print(child_1).to_string(), after_detach_child_1);
    /// ```
    #[inline]
    pub fn detach(&mut self, node: Id) {
        self.hierarchy.detach(node.to_internal());
    }

    /// Detaches the node from neighbors and make it orphan root.
    ///
    /// Children are inserted to the place where the detached node was.
    ///
    /// If you want to detach not single node but subtree, use
    /// [`detach`][`Self::detach`] method.
    ///
    /// # Errors
    ///
    /// Returns [`StructureError::SiblingsWithoutParent`] when the node has
    /// multiple children but has no parent.
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
    ///
    /// # Examples
    ///
    /// ```
    /// # use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
    /// # let mut forest = Forest::<NodeIdUsize, _>::new();
    /// # let mut builder = ChainTreeBuilder::new(&mut forest, "root");
    /// # let child_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .current_id();
    /// # builder
    /// #     .child("1-0")
    /// #     .sibling("1-1")
    /// #     .sibling("1-2")
    /// #     .parent()
    /// #     .sibling("2");
    /// # let root = builder.root_id();
    /// let before = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), before);
    ///
    /// // Detach the single node "1".
    /// forest.detach_single(child_1);
    ///
    /// let after_detach_root = r#"root
    /// |-- 0
    /// |-- 1-0
    /// |-- 1-1
    /// |-- 1-2
    /// `-- 2"#;
    /// let after_detach_child_1 = "1";
    /// assert_eq!(forest.debug_print(root).to_string(), after_detach_root);
    /// assert_eq!(forest.debug_print(child_1).to_string(), after_detach_child_1);
    /// ```
    #[inline]
    pub fn detach_single(&mut self, node: Id) -> Result<(), StructureError> {
        self.hierarchy.detach_single(node.to_internal())
    }

    /// Removes the subtree from the forest.
    ///
    /// Data of each node is passed to the function `f` before removed from
    /// the forest. The order of the node traversal is postorder.
    ///
    /// # Panic safety
    ///
    /// This method is panic safe, i.e. the forest and arena remains consistent
    /// even when the given function panics.
    ///
    /// However, this safety is for panicking argument. If the crate itself has
    /// a bug and panics with assertion failure, no consistency guarantees are
    /// provided of course.
    ///
    /// Note that being panic-safe introduces extra cost. If you won't use the
    /// forest after the panic happens, use more efficient but panic-unsafe
    /// version, [`remove_hooked`][`Self::remove_hooked`].
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive, i.e. has been already removed or
    /// does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// # use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
    /// # let mut forest = Forest::<NodeIdUsize, _>::new();
    /// # let mut builder = ChainTreeBuilder::new(&mut forest, "root");
    /// # let child_1_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .child("1-0")
    /// #     .sibling("1-1")
    /// #     .current_id();
    /// # builder
    /// #     .child("1-1-0")
    /// #     .sibling("1-1-1")
    /// #     .sibling("1-1-2")
    /// #     .parent()
    /// #     .sibling("1-2")
    /// #     .parent()
    /// #     .sibling("2");
    /// # let root = builder.root_id();
    /// let before = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   |   |-- 1-1-0
    /// |   |   |-- 1-1-1
    /// |   |   `-- 1-1-2
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), before);
    ///
    /// let mut removed_data = Vec::new();
    ///
    /// // Remove "1-1" and its descendant.
    /// forest.remove_hooked_panic_safe(child_1_1, |data| {
    ///     removed_data.push(data);
    /// });
    ///
    /// let after_remove = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), after_remove);
    /// assert_eq!(removed_data, &["1-1-0", "1-1-1", "1-1-2", "1-1"]);
    /// ```
    pub fn remove_hooked_panic_safe<F: FnMut(T)>(&mut self, node: Id, f: F) {
        /// Implementation that depends on `Id::Internal` instead of `NodeId`
        /// in order to reduce monomorphization and prevent binary bloat.
        fn inner<InternalId: InternalNodeId, T, F: FnMut(T)>(
            hierarchy: &mut Hierarchy<InternalId>,
            data: &mut [Option<T>],
            node: InternalId,
            mut f: F,
        ) {
            if !hierarchy.is_alive(node) {
                return;
            }
            hierarchy.detach(node);

            let mut traverser = SafeModeDepthFirstTraverser::new(node, hierarchy);
            while let Some(ev) = traverser.next(hierarchy) {
                let id = match ev {
                    DftEvent::Open(_) => continue,
                    DftEvent::Close(id) => id,
                };

                // Detach the leaf node.
                debug_assert!(
                    hierarchy
                        .neighbors(id)
                        .expect("[consistency] the current node must be alive here")
                        .first_child()
                        .is_none(),
                    "[consistency] the node must be the leaf"
                );
                hierarchy.detach(id);
                let nbs = hierarchy
                    .neighbors_mut(id)
                    .expect("[consistency] the current node must be alive here");
                debug_assert!(
                    nbs.is_alone(),
                    "[consistency] the detached leaf node must be alone"
                );
                nbs.make_removed();
                let elem = data[id.to_usize()]
                    .take()
                    .expect("[consistency] the node must have an associated data");
                f(elem);
            }
        }

        inner(&mut self.hierarchy, &mut self.data, node.to_internal(), f)
    }

    /// Removes the subtree from the forest.
    ///
    /// Data of each node is passed to the function `f` before removed from
    /// the forest. The order of the node traversal is postorder.
    ///
    /// Note that the forest and arena will be inconsistent once the given
    /// function panics. In other words, panicking of the given function make
    /// the forest lose any guarantee of correctness and availability.
    ///
    /// If you want to refer the forest even when panic happens, use panic-safe
    /// version [`remove_hooked_panic_safe`][`Self::remove_hooked_panic_safe`].
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive, i.e. has been already removed or
    /// does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// # use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
    /// # let mut forest = Forest::<NodeIdUsize, _>::new();
    /// # let mut builder = ChainTreeBuilder::new(&mut forest, "root");
    /// # let child_1_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .child("1-0")
    /// #     .sibling("1-1")
    /// #     .current_id();
    /// # builder
    /// #     .child("1-1-0")
    /// #     .sibling("1-1-1")
    /// #     .sibling("1-1-2")
    /// #     .parent()
    /// #     .sibling("1-2")
    /// #     .parent()
    /// #     .sibling("2");
    /// # let root = builder.root_id();
    /// let before = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   |   |-- 1-1-0
    /// |   |   |-- 1-1-1
    /// |   |   `-- 1-1-2
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), before);
    ///
    /// let mut removed_data = Vec::new();
    ///
    /// // Remove "1-1" and its descendant.
    /// forest.remove_hooked(child_1_1, |data| {
    ///     removed_data.push(data);
    /// });
    ///
    /// let after_remove = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), after_remove);
    /// assert_eq!(removed_data, &["1-1-0", "1-1-1", "1-1-2", "1-1"]);
    /// ```
    pub fn remove_hooked<F: FnMut(T)>(&mut self, node: Id, f: F) {
        /// Implementation that depends on `Id::Internal` instead of `NodeId`
        /// in order to reduce monomorphization and prevent binary bloat.
        fn inner<InternalId: InternalNodeId, T, F: FnMut(T)>(
            hierarchy: &mut Hierarchy<InternalId>,
            data: &mut [Option<T>],
            node: InternalId,
            mut f: F,
        ) {
            if !hierarchy.is_alive(node) {
                return;
            }
            hierarchy.detach(node);

            let mut traverser = SafeModeDepthFirstTraverser::new(node, hierarchy);
            while let Some(ev) = traverser.next(hierarchy) {
                let id = match ev {
                    DftEvent::Open(_) => continue,
                    DftEvent::Close(id) => id,
                };

                // Break the node. The tree will be temporarily inconsistent.
                let nbs = hierarchy
                    .neighbors_mut(id)
                    .expect("[consistency] the current node must be alive here");
                nbs.force_make_removed();
                let data = data[id.to_usize()]
                    .take()
                    .expect("[consistency] the node must have an associated data");
                f(data);
            }
            // At this point, all nodes under the `node` are removed.
            // Now the forest must be totally consistent.
        }
        inner(&mut self.hierarchy, &mut self.data, node.to_internal(), f);
    }

    /// Removes the subtree from the forest.
    ///
    /// Data associated to the nodes being removed are simply discarded.
    /// If you want to take or use them out of the forest, use
    /// [`remove_hooked`][`Self::remove_hooked`] method or
    /// [`remove_hooked_panic_safe`][`Self::remove_hooked_panic_safe`] instead.
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive, i.e. has been already removed or
    /// does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// # use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
    /// # let mut forest = Forest::<NodeIdUsize, _>::new();
    /// # let mut builder = ChainTreeBuilder::new(&mut forest, "root");
    /// # let child_1_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .child("1-0")
    /// #     .sibling("1-1")
    /// #     .current_id();
    /// # builder
    /// #     .child("1-1-0")
    /// #     .sibling("1-1-1")
    /// #     .sibling("1-1-2")
    /// #     .parent()
    /// #     .sibling("1-2")
    /// #     .parent()
    /// #     .sibling("2");
    /// # let root = builder.root_id();
    /// let before = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   |   |-- 1-1-0
    /// |   |   |-- 1-1-1
    /// |   |   `-- 1-1-2
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), before);
    ///
    /// // Remove "1-1" and its descendant.
    /// // Data associated to nodes (4 string slices in this case)
    /// // are simply discarded.
    /// forest.remove(child_1_1);
    ///
    /// let after_remove = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), after_remove);
    /// ```
    #[inline]
    pub fn remove(&mut self, node: Id) {
        self.remove_hooked(node, drop);
    }
}

/// Iteration.
impl<Id: NodeId, T> Forest<Id, T> {
    /// Returns a depth-first traversal iterator of a subtree.
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{DftEvent, Forest, InsertAs, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let root = forest.create_root("root");
    /// let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// forest.create_insert("0-0", InsertAs::LastChildOf(child0));
    /// forest.create_insert("1", InsertAs::LastChildOf(root));
    ///
    /// assert_eq!(
    ///     forest
    ///         .depth_first_traverse(root)
    ///         .map(|ev| ev.map(|node| *node.data()))
    ///         .collect::<Vec<_>>(),
    ///     &[
    ///         DftEvent::Open("root"),
    ///         DftEvent::Open("0"),
    ///         DftEvent::Open("0-0"),
    ///         DftEvent::Close("0-0"),
    ///         DftEvent::Close("0"),
    ///         DftEvent::Open("1"),
    ///         DftEvent::Close("1"),
    ///         DftEvent::Close("root"),
    ///     ]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn depth_first_traverse(&self, node: Id) -> traverse::DepthFirstTraverse<'_, Id, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .depth_first_traverse()
    }

    /// Returns a depth-first traversal iterator of a subtree.
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{DftEvent, Forest, InsertAs, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let root = forest.create_root("root");
    /// let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// let child00 = forest.create_insert("0-0", InsertAs::LastChildOf(child0));
    /// forest.create_insert("0-0-0", InsertAs::LastChildOf(child00));
    /// forest.create_insert("0-1", InsertAs::LastChildOf(child0));
    /// forest.create_insert("1", InsertAs::LastChildOf(root));
    ///
    /// // root
    /// // |-- 0
    /// // |   |-- 0-0
    /// // |   |   `-- 0-0-0
    /// // |   `-- 0-1
    /// // `-- 1
    ///
    /// assert_eq!(
    ///     forest
    ///         .shallow_depth_first_traverse(root, Some(2))
    ///         .map(|(ev, depth)| (ev.map(|node| *node.data()), depth))
    ///         .collect::<Vec<_>>(),
    ///     &[
    ///         (DftEvent::Open("root"), 0),
    ///         (DftEvent::Open("0"), 1),
    ///         (DftEvent::Open("0-0"), 2),
    ///         (DftEvent::Close("0-0"), 2),
    ///         // Note that `0-0-0` node is not traversed since its depth is 3.
    ///         (DftEvent::Open("0-1"), 2),
    ///         (DftEvent::Close("0-1"), 2),
    ///         (DftEvent::Close("0"), 1),
    ///         (DftEvent::Open("1"), 1),
    ///         (DftEvent::Close("1"), 1),
    ///         (DftEvent::Close("root"), 0),
    ///     ]
    /// );
    /// ```
    ///
    /// Depth is counted from the start of traversal, not from the true root node.
    ///
    /// ```
    /// use treena::dynamic::{DftEvent, Forest, InsertAs, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let root = forest.create_root("root");
    /// let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// let child00 = forest.create_insert("0-0", InsertAs::LastChildOf(child0));
    /// forest.create_insert("0-0-0", InsertAs::LastChildOf(child00));
    /// forest.create_insert("0-1", InsertAs::LastChildOf(child0));
    /// forest.create_insert("1", InsertAs::LastChildOf(root));
    ///
    /// // root
    /// // |-- 0
    /// // |   |-- 0-0
    /// // |   |   `-- 0-0-0
    /// // |   `-- 0-1
    /// // `-- 1
    ///
    /// assert_eq!(
    ///     forest
    ///         .shallow_depth_first_traverse(child0, Some(1))
    ///         .map(|(ev, depth)| (ev.map(|node| *node.data()), depth))
    ///         .collect::<Vec<_>>(),
    ///     &[
    ///         (DftEvent::Open("0"), 0),
    ///         (DftEvent::Open("0-0"), 1),
    ///         (DftEvent::Close("0-0"), 1),
    ///         // Note that `0-0-0` node is not traversed since its depth is 2.
    ///         (DftEvent::Open("0-1"), 1),
    ///         (DftEvent::Close("0-1"), 1),
    ///         (DftEvent::Close("0"), 0),
    ///     ]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn shallow_depth_first_traverse(
        &self,
        node: Id,
        max_depth: Option<usize>,
    ) -> traverse::ShallowDepthFirstTraverse<'_, Id, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .shallow_depth_first_traverse(max_depth)
    }

    /// Returns a breadth-first traversal iterator of a subtree.
    ///
    /// This iterator does not heap-allocates but iterating all nodes will be
    /// `O(n^2)` operation in worst case, not `O(n)`.
    /// If you want more efficient traversal, use
    /// [`AllocatingBreadthFirstTraverse`] returned by
    /// [`Forest::allocating_breadth_first_traverse`] method.
    ///
    /// [`AllocatingBreadthFirstTraverse`]:
    ///     `traverse::AllocatingBreadthFirstTraverse`
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, InsertAs, NodeIdUsize, ChainTreeBuilder};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let root = ChainTreeBuilder::new(&mut forest, "root")
    ///     .child("0")
    ///     .child("0-0")
    ///     .child("0-0-0")
    ///     .parent()
    ///     .sibling("0-1")
    ///     .child("0-1-0")
    ///     .sibling("0-1-1")
    ///     .parent()
    ///     .parent()
    ///     .sibling("1")
    ///     .child("1-0")
    ///     .sibling("1-1")
    ///     .root_id();
    ///
    /// // root
    /// // |-- 0
    /// // |   |-- 0-0
    /// // |   |   `-- 0-0-0
    /// // |   `-- 0-1
    /// // |       |-- 0-1-0
    /// // |       `-- 0-1-1
    /// // `-- 1
    /// //     |-- 1-0
    /// //     `-- 1-1
    ///
    /// assert_eq!(
    ///     forest
    ///         .breadth_first_traverse(root)
    ///         .map(|(node, depth)| (*node.data(), depth))
    ///         .collect::<Vec<_>>(),
    ///     &[
    ///         ("root", 0),
    ///         ("0", 1),
    ///         ("1", 1),
    ///         ("0-0", 2),
    ///         ("0-1", 2),
    ///         ("1-0", 2),
    ///         ("1-1", 2),
    ///         ("0-0-0", 3),
    ///         ("0-1-0", 3),
    ///         ("0-1-1", 3),
    ///     ]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn breadth_first_traverse(&self, node: Id) -> traverse::BreadthFirstTraverse<'_, Id, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .breadth_first_traverse()
    }

    /// Returns an allocating breadth-first traversal iterator of a subtree.
    ///
    /// This iterator heap-allocates and `.next()` performs better than
    /// [`BreadthFirstTraverse`] returned by
    /// [`Forest::breadth_first_traverse`] method.
    ///
    /// [`BreadthFirstTraverse`]: `traverse::BreadthFirstTraverse`
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, InsertAs, NodeIdUsize, ChainTreeBuilder};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let root = ChainTreeBuilder::new(&mut forest, "root")
    ///     .child("0")
    ///     .child("0-0")
    ///     .child("0-0-0")
    ///     .parent()
    ///     .sibling("0-1")
    ///     .child("0-1-0")
    ///     .sibling("0-1-1")
    ///     .parent()
    ///     .parent()
    ///     .sibling("1")
    ///     .child("1-0")
    ///     .sibling("1-1")
    ///     .root_id();
    ///
    /// // root
    /// // |-- 0
    /// // |   |-- 0-0
    /// // |   |   `-- 0-0-0
    /// // |   `-- 0-1
    /// // |       |-- 0-1-0
    /// // |       `-- 0-1-1
    /// // `-- 1
    /// //     |-- 1-0
    /// //     `-- 1-1
    ///
    /// assert_eq!(
    ///     forest
    ///         .allocating_breadth_first_traverse(root)
    ///         .map(|(node, depth)| (*node.data(), depth))
    ///         .collect::<Vec<_>>(),
    ///     &[
    ///         ("root", 0),
    ///         ("0", 1),
    ///         ("1", 1),
    ///         ("0-0", 2),
    ///         ("0-1", 2),
    ///         ("1-0", 2),
    ///         ("1-1", 2),
    ///         ("0-0-0", 3),
    ///         ("0-1-0", 3),
    ///         ("0-1-1", 3),
    ///     ]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn allocating_breadth_first_traverse(
        &self,
        node: Id,
    ) -> traverse::AllocatingBreadthFirstTraverse<'_, Id, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .allocating_breadth_first_traverse()
    }

    /// Returns an iterator of ancestors, excluding this node.
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, InsertAs, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let root = forest.create_root("root");
    /// let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// let child00 = forest.create_insert("0-0", InsertAs::LastChildOf(child0));
    ///
    /// assert_eq!(
    ///     forest
    ///         .ancestors(child00)
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["0", "root"]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn ancestors(&self, node: Id) -> traverse::Ancestors<'_, Id, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .ancestors()
    }

    /// Returns an iterator of ancestors, including this node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, InsertAs, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let root = forest.create_root("root");
    /// let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// let child00 = forest.create_insert("0-0", InsertAs::LastChildOf(child0));
    ///
    /// assert_eq!(
    ///     forest
    ///         .ancestors_or_self(child00)
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["0-0", "0", "root"]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn ancestors_or_self(&self, node: Id) -> traverse::Ancestors<'_, Id, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .ancestors_or_self()
    }

    /// Returns an iterator of children.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{DftEvent, Forest, InsertAs, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let root = forest.create_root("root");
    /// let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// let child00 = forest.create_insert("0-0", InsertAs::LastChildOf(child0));
    /// forest.create_insert("1", InsertAs::LastChildOf(root));
    /// forest.create_insert("2", InsertAs::LastChildOf(root));
    ///
    /// assert_eq!(
    ///     forest
    ///         .children(root)
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["0", "1", "2"]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn children(&self, node: Id) -> traverse::Siblings<'_, Id, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .children()
    }

    /// Returns an iterator of the following siblings, excluding this node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, InsertAs, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let root = forest.create_root("root");
    /// let _child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// let child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    /// let _child2 = forest.create_insert("2", InsertAs::LastChildOf(root));
    ///
    /// assert_eq!(
    ///     forest
    ///         .following_siblings(child1)
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["2"]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn following_siblings(&self, node: Id) -> traverse::Siblings<'_, Id, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .following_siblings()
    }

    /// Returns an iterator of the following siblings, including this node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, InsertAs, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let root = forest.create_root("root");
    /// let _child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// let child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    /// let _child2 = forest.create_insert("2", InsertAs::LastChildOf(root));
    ///
    /// assert_eq!(
    ///     forest
    ///         .following_siblings_or_self(child1)
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["1", "2"]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn following_siblings_or_self(&self, node: Id) -> traverse::Siblings<'_, Id, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .following_siblings_or_self()
    }

    /// Returns an iterator of the preceding siblings, excluding this node.
    ///
    /// Note that this iterates nodes in order from first child to last child.
    /// If you want to the reverse-order iterator, use [`Iterator::rev`].
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, InsertAs, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let root = forest.create_root("root");
    /// let _child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// let _child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    /// let child2 = forest.create_insert("2", InsertAs::LastChildOf(root));
    /// let _child3 = forest.create_insert("3", InsertAs::LastChildOf(root));
    ///
    /// assert_eq!(
    ///     forest
    ///         .preceding_siblings(child2)
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["0", "1"]
    /// );
    /// assert_eq!(
    ///     forest
    ///         .preceding_siblings(child2)
    ///         .rev() // REVERSED!
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["1", "0"],
    ///     "Use `.rev()` to iterate from the starting node to the first node"
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn preceding_siblings(&self, node: Id) -> traverse::Siblings<'_, Id, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .preceding_siblings()
    }

    /// Returns an iterator of the preceding siblings, including this node.
    ///
    /// Note that this iterates nodes in order from first child to last child.
    /// If you want to the reverse-order iterator, use [`Iterator::rev`].
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, InsertAs, NodeIdUsize};
    ///
    /// let mut forest = Forest::<NodeIdUsize, _>::new();
    /// let root = forest.create_root("root");
    /// let _child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// let _child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    /// let child2 = forest.create_insert("2", InsertAs::LastChildOf(root));
    /// let _child3 = forest.create_insert("3", InsertAs::LastChildOf(root));
    ///
    /// assert_eq!(
    ///     forest
    ///         .preceding_siblings_or_self(child2)
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["0", "1", "2"]
    /// );
    /// assert_eq!(
    ///     forest
    ///         .preceding_siblings_or_self(child2)
    ///         .rev() // REVERSED!
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["2", "1", "0"],
    ///     "Use `.rev()` to iterate from the starting node to the first node"
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn preceding_siblings_or_self(&self, node: Id) -> traverse::Siblings<'_, Id, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .preceding_siblings_or_self()
    }
}

/// Tree cloning.
impl<Id: NodeId, T: Clone> Forest<Id, T> {
    /// Clones a subtree as a new tree in the forest, and returns the new root ID.
    ///
    /// # Panics
    ///
    /// Panics if the node (including descendants) are not alive.
    ///
    /// # Examples
    ///
    /// ```
    /// # use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
    /// # let mut forest = Forest::<NodeIdUsize, _>::new();
    /// # let mut builder = ChainTreeBuilder::new(&mut forest, "root");
    /// # let child_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .current_id();
    /// # builder
    /// #     .child("1-0")
    /// #     .sibling("1-1")
    /// #     .sibling("1-2")
    /// #     .parent()
    /// #     .sibling("2");
    /// # let root = builder.root_id();
    /// let before = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), before);
    ///
    /// // Clone a tree.
    /// let cloned = forest.clone_local_tree(child_1);
    ///
    /// let cloned_expected = r#"1
    /// |-- 1-0
    /// |-- 1-1
    /// `-- 1-2"#;
    /// assert_eq!(forest.debug_print(cloned).to_string(), cloned_expected);
    /// assert!(
    ///     forest.node(cloned).expect("must be alive").parent_id().is_none(),
    ///     "The new node is a root node of an independent tree and has no parent"
    /// );
    /// ```
    #[must_use = "newly created node cannot be accessed without the returned node ID"]
    pub fn clone_local_tree(&mut self, src_id: Id) -> Id {
        self.clone_local_tree_with_id_mapping(src_id, |_, _| ())
    }

    /// Clones a subtree from another forest as a new tree, and returns the new
    /// root ID in this forest.
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
    ///
    /// # Examples
    ///
    /// ```
    /// # use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
    /// # let mut forest_src = Forest::<NodeIdUsize, _>::new();
    /// # let mut builder = ChainTreeBuilder::new(&mut forest_src, "root");
    /// # let child_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .current_id();
    /// # builder
    /// #     .child("1-0")
    /// #     .sibling("1-1")
    /// #     .sibling("1-2")
    /// #     .parent()
    /// #     .sibling("2");
    /// # let root = builder.root_id();
    /// let before = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest_src.debug_print(root).to_string(), before);
    ///
    /// // Destination forest.
    /// let mut forest_dest = Forest::<NodeIdUsize, _>::new();
    ///
    /// // Clone a tree.
    /// let tree_src = forest_src.node(child_1).expect("the node is available");
    /// let cloned = forest_dest.clone_foreign_tree(tree_src);
    ///
    /// let cloned_expected = r#"1
    /// |-- 1-0
    /// |-- 1-1
    /// `-- 1-2"#;
    /// assert_eq!(forest_dest.debug_print(cloned).to_string(), cloned_expected);
    /// assert!(
    ///     forest_dest.node(cloned).expect("must be alive").parent_id().is_none(),
    ///     "The new node is a root node of an independent tree and has no parent"
    /// );
    /// ```
    #[must_use = "newly created node cannot be accessed without the returned node ID"]
    pub fn clone_foreign_tree(&mut self, src_root: Node<'_, Id, T>) -> Id {
        self.clone_foreign_tree_with_id_mapping(src_root, |_, _| ())
    }

    /// Clones a subtree as a new tree in the forest, and returns the new root ID.
    ///
    /// # Panics
    ///
    /// Panics if the node (including descendants) are not alive.
    ///
    /// # Examples
    ///
    /// ```
    /// # use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
    /// # let mut forest = Forest::<NodeIdUsize, _>::new();
    /// # let mut builder = ChainTreeBuilder::new(&mut forest, "root");
    /// # let child_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .current_id();
    /// # builder
    /// #     .child("1-0")
    /// #     .sibling("1-1")
    /// #     .sibling("1-2")
    /// #     .parent()
    /// #     .sibling("2");
    /// # let root = builder.root_id();
    /// let before = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), before);
    ///
    /// // Clone a tree.
    /// let mut mapping = Vec::new();
    /// let cloned = forest.clone_local_tree_with_id_mapping(
    ///     child_1,
    ///     |src, dest| mapping.push((src, dest))
    /// );
    ///
    /// let cloned_expected = r#"1
    /// |-- 1-0
    /// |-- 1-1
    /// `-- 1-2"#;
    /// assert_eq!(forest.debug_print(cloned).to_string(), cloned_expected);
    /// assert!(
    ///     forest.node(cloned).expect("must be alive").parent_id().is_none(),
    ///     "The new node is a root node of an independent tree and has no parent"
    /// );
    ///
    /// // Check node ID mapping.
    /// for (src, dest) in mapping {
    ///     assert_eq!(forest.data(src), forest.data(dest));
    /// }
    /// ```
    #[must_use = "newly created node cannot be accessed without the returned node ID"]
    pub fn clone_local_tree_with_id_mapping<F>(&mut self, src_id: Id, mut add_mapping: F) -> Id
    where
        F: FnMut(Id, Id),
    {
        /// Clones the next node.
        ///
        /// Returns `Option<SourceId>`.
        ///
        /// Implementation that depends on `Id::Internal` instead of `NodeId`
        /// in order to reduce monomorphization and prevent binary bloat.
        fn clone_next_node<InternalId: InternalNodeId, T: Clone>(
            hierarchy: &mut Hierarchy<InternalId>,
            data: &mut Vec<Option<T>>,
            current_dest: &mut InternalId,
            traverser: &mut SafeModeDepthFirstTraverser<InternalId>,
        ) -> Option<InternalId> {
            while let Some(ev) = traverser.next(hierarchy) {
                match ev {
                    DftEvent::Open(src_id) => {
                        let node_data = data
                            .get(src_id.to_usize())
                            .cloned()
                            .expect("[consistency] the node being traversed must be alive")
                            .expect("[consistency] the node being traversed must be alive");
                        *current_dest = create_insert_momo(
                            hierarchy,
                            data,
                            node_data,
                            InsertAs::LastChildOf(*current_dest),
                        );
                        return Some(src_id);
                    }
                    DftEvent::Close(_) => {
                        let parent = hierarchy
                            .neighbors(*current_dest)
                            .expect("[consistency] the node being created must be alive")
                            .parent();
                        *current_dest = match parent {
                            Some(id) => id,
                            None => return None,
                        }
                    }
                }
            }
            unreachable!("[consistency] traversal must end with the closing of the root node");
        }

        let root_data = self
            .data(src_id)
            .expect("[consistency] the node must be alive")
            .clone();
        let root_id = self.create_root(root_data);
        add_mapping(src_id, root_id);
        let mut traverser = SafeModeDepthFirstTraverser::new(src_id.to_internal(), &self.hierarchy);

        // Skip the open event of the root node.
        let _ = traverser.next(&self.hierarchy);

        // Clone descendants.
        let mut current_dest = root_id.to_internal();
        while let Some(src_id) = clone_next_node(
            &mut self.hierarchy,
            &mut self.data,
            &mut current_dest,
            &mut traverser,
        ) {
            add_mapping(Id::from_internal(src_id), Id::from_internal(current_dest));
        }

        assert_eq!(
            Id::from_internal(current_dest),
            root_id,
            "[consistency] all nodes including the root must have been closed"
        );

        root_id
    }

    /// Clones a subtree from another forest as a new tree, and returns the new
    /// root ID in this forest.
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
    ///
    /// # Examples
    ///
    /// ```
    /// # use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
    /// # let mut forest_src = Forest::<NodeIdUsize, _>::new();
    /// # let mut builder = ChainTreeBuilder::new(&mut forest_src, "root");
    /// # let child_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .current_id();
    /// # builder
    /// #     .child("1-0")
    /// #     .sibling("1-1")
    /// #     .sibling("1-2")
    /// #     .parent()
    /// #     .sibling("2");
    /// # let root = builder.root_id();
    /// let before = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest_src.debug_print(root).to_string(), before);
    ///
    /// // Destination forest.
    /// let mut forest_dest = Forest::<NodeIdUsize, _>::new();
    ///
    /// // Clone a tree.
    /// let tree_src = forest_src.node(child_1).expect("the node is available");
    /// let mut mapping = Vec::new();
    /// let cloned = forest_dest.clone_foreign_tree_with_id_mapping(
    ///     tree_src,
    ///     |src, dest| mapping.push((src, dest))
    /// );
    ///
    /// let cloned_expected = r#"1
    /// |-- 1-0
    /// |-- 1-1
    /// `-- 1-2"#;
    /// assert_eq!(forest_dest.debug_print(cloned).to_string(), cloned_expected);
    /// assert!(
    ///     forest_dest.node(cloned).expect("must be alive").parent_id().is_none(),
    ///     "The new node is a root node of an independent tree and has no parent"
    /// );
    ///
    /// // Check node ID mapping.
    /// for (src, dest) in mapping {
    ///     assert_eq!(forest_src.data(src), forest_dest.data(dest));
    /// }
    /// ```
    #[must_use = "newly created node cannot be accessed without the returned node ID"]
    pub fn clone_foreign_tree_with_id_mapping<F>(
        &mut self,
        src_root: Node<'_, Id, T>,
        mut add_mapping: F,
    ) -> Id
    where
        F: FnMut(Id, Id),
    {
        /// Clones the next node.
        ///
        /// Returns `Option<SourceId>`.
        ///
        /// Implementation that depends on `Id::Internal` instead of `NodeId`
        /// in order to reduce monomorphization and prevent binary bloat.
        fn clone_next_node<InternalId: InternalNodeId, T: Clone>(
            hierarchy_dest: &mut Hierarchy<InternalId>,
            data_dest: &mut Vec<Option<T>>,
            current_dest: &mut InternalId,
            hierarchy_src: &Hierarchy<InternalId>,
            src_traverser: &mut DepthFirstTraverser<InternalId>,
            data_src: &[Option<T>],
        ) -> Option<InternalId> {
            while let Some(ev) = src_traverser.next(hierarchy_src) {
                match ev {
                    DftEvent::Open(src_id) => {
                        let node_data = data_src
                            .get(src_id.to_usize())
                            .cloned()
                            .expect("[consistency] the node being traversed must be alive")
                            .expect("[consistency] the node being traversed must be alive");
                        *current_dest = create_insert_momo(
                            hierarchy_dest,
                            data_dest,
                            node_data,
                            InsertAs::LastChildOf(*current_dest),
                        );
                        return Some(src_id);
                    }
                    DftEvent::Close(_) => {
                        match hierarchy_dest
                            .neighbors(*current_dest)
                            .expect("[consistency] the node must be created recently and alive")
                            .parent()
                        {
                            Some(parent) => {
                                *current_dest = parent;
                                continue;
                            }
                            None => {
                                // Closing root node.
                                return None;
                            }
                        }
                    }
                }
            }
            unreachable!("[consistency] traversal must end with the closing of the root node");
        }

        let root_data = src_root.data().clone();
        let root_dest_id = self.create_root(root_data);
        let hierarchy_src = &src_root.forest().hierarchy;
        add_mapping(src_root.id(), root_dest_id);
        let mut src_traverser =
            DepthFirstTraverser::with_toplevel(src_root.id().to_internal(), hierarchy_src);

        // Skip the open event of the root node.
        let _ = src_traverser.next(hierarchy_src);

        // Clone descendants.
        let mut current_dest = root_dest_id.to_internal();
        while let Some(src_id) = clone_next_node(
            &mut self.hierarchy,
            &mut self.data,
            &mut current_dest,
            hierarchy_src,
            &mut src_traverser,
            &src_root.forest().data,
        ) {
            add_mapping(Id::from_internal(src_id), Id::from_internal(current_dest));
        }

        assert_eq!(
            Id::from_internal(current_dest),
            root_dest_id,
            "[consistency] traversal must end with the closing of the destination root node"
        );
        assert_eq!(
            src_traverser.next(hierarchy_src),
            None,
            "[consistency] traversal must also end with the closing of the source root node"
        );

        root_dest_id
    }
}

/// Debug printing.
impl<Id: NodeId, T> Forest<Id, T> {
    /// Returns the pretty-printable proxy object to the node and descendants.
    pub fn debug_print(&self, id: Id) -> debug_print::DebugPrint<'_, Id, T> {
        let node = self
            .node(id)
            .expect("[precondition] the node must be alive");
        debug_print::DebugPrint::new(node)
    }
}

impl<Id: NodeId, T> Default for Forest<Id, T> {
    fn default() -> Self {
        Self {
            hierarchy: Default::default(),
            data: Default::default(),
        }
    }
}

/// Creates a node and inserts it to the target position.
///
/// For the spec and limitations, see [`Forest::create_insert`].
///
/// Implementation that depends on `Id::Internal` instead of `NodeId`
/// in order to reduce monomorphization and prevent binary bloat.
// To avoid duplicate document that is hard to maintain, specs are described
// in the doc comments for `Forest::create_insert`.
fn create_insert_momo<Id: InternalNodeId, T>(
    hierarchy: &mut Hierarchy<Id>,
    storage: &mut Vec<Option<T>>,
    data: T,
    dest: InsertAs<Id>,
) -> Id {
    assert!(
        hierarchy.is_valid(dest.to_anchor()),
        "[precondition] the anchor must be valid for this forest"
    );
    let new_id = hierarchy.create_root();
    storage.push(Some(data));
    // This insert must not fail if the anchor of `dest` is alive and from the forest.
    // If the anchor is not alive, `insert()` itself panics.
    //
    // If the anchor is from other forest but accidentally valid as the node ID
    // as this forest, `insert()` could return `Err(_)`.
    hierarchy.insert(new_id, dest).expect(
        "[precondition] newly created node is independent from the destination \
         and the anchor has been valid before the new node is created",
    );

    new_id
}

/// Structure inconsistency error.
#[derive(Debug, Clone, Copy)]
pub enum StructureError {
    /// Attempt to make a node the ancestor of itself.
    AncestorDescendantLoop,
    /// Attempt to make a node the sibling of itself.
    UnorderableSiblings,
    /// Attempt to add sibling nodes without a parent.
    SiblingsWithoutParent,
}

impl fmt::Display for StructureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match *self {
            Self::AncestorDescendantLoop => "attempt to make a node the ancestor of itself",
            Self::UnorderableSiblings => "attempt to make a node the sibling of itself",
            Self::SiblingsWithoutParent => "attempt to add sibling nodes without a parent",
        };
        f.write_str(msg)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for StructureError {}

#[cfg(test)]
mod tests {
    use super::*;

    /// Ensures that functions defined in functions are monomorphized
    /// independently without considering outer function's type parameters.
    ///
    /// This is in fact testing compiler's behavior, rather than the
    /// implementation of this crate.
    ///
    /// This fact is useful to reduce monomorphization.
    ///
    /// `Forest<Id, T>` is a pair of `Hierarchy<Id::Internal>` and `Vec<T>`, and
    /// most of the operations provided from `Forest<Id, T>` actually depends on
    /// `T` and `Id::Internal`, not `Id`.
    /// `Id` is only necessary to make parameter types and return types
    /// different, and the internal logic is almost identical when
    /// `Id::Internal` is the same.
    ///
    /// For example, internal implementantion of `Forest::<Id0, T>::remove` and
    /// `Forest::<Id1, T>::remove` can be almost the same when `Id0::Internal`
    /// and `Id1::Internal` are the same type, except the part that converts
    /// `Id0` or `Id1` into `_::Internal` type value.
    #[test]
    fn ensure_inner_function_is_monomorphized() {
        use core::any::Any;

        use crate::dynamic::{InternalNodeId, NodeIdUsize};
        use crate::impl_dynamic_node_id;

        // Dummy struct mimicking `Forest<Id: NdoeId, T>`.
        struct MyContainer<Id: NodeId, T> {
            _ids: Vec<Id::Internal>,
            _values: Vec<T>,
        }
        impl<Id: NodeId, T> Default for MyContainer<Id, T> {
            fn default() -> Self {
                Self {
                    _ids: Default::default(),
                    _values: Default::default(),
                }
            }
        }

        impl<Id: NodeId, T> MyContainer<Id, T> {
            fn new() -> Self {
                Self::default()
            }

            fn inner_fn_addr(&self) -> fn(Id::Internal) -> () {
                fn inner<I: InternalNodeId>(_: I) {}

                inner::<Id::Internal> as fn(Id::Internal) -> ()
            }
        }

        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        struct MyId0(NodeIdUsize);
        impl_dynamic_node_id!(MyId0, NodeIdUsize, 0);

        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        struct MyId1(NodeIdUsize);
        impl_dynamic_node_id!(MyId1, NodeIdUsize, 0);

        let container0 = MyContainer::<MyId0, usize>::new();
        let container1 = MyContainer::<MyId1, usize>::new();

        let outer_addr0 = MyContainer::<MyId0, usize>::inner_fn_addr as fn(_) -> _;
        let outer_addr1 = MyContainer::<MyId1, usize>::inner_fn_addr as fn(_) -> _;

        assert_ne!(
            outer_addr0.type_id(),
            outer_addr1.type_id(),
            "outer functions must have different types"
        );
        assert_eq!(
            container0.inner_fn_addr(),
            container1.inner_fn_addr(),
            "inner functions must have the same address \
             while the outer functions are different"
        );
    }
}
