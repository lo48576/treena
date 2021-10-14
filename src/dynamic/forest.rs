//! Forest.

mod builder;
#[cfg(any(feature = "debug-print"))]
mod debug_print;
mod node;
pub(crate) mod traverse;

use core::fmt;

use alloc::vec::Vec;

use crate::dynamic::hierarchy::traverse::{DftEvent, SafeModeDepthFirstTraverser};
use crate::dynamic::hierarchy::{Hierarchy, Neighbors};
use crate::dynamic::{InsertAs, NodeId};

pub use self::builder::TreeBuilder;
#[cfg(any(feature = "debug-print"))]
pub use self::debug_print::DebugPrint;
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
/// use treena::dynamic::Forest;
///
/// // Usually you want the forest to be `mut` to modify structure.
/// let forest = Forest::<i64>::new();
/// ```
///
/// ## Building tree and modifying structure
///
/// There are some ways to construct a tree and/or rebuild trees.
///
/// **[`TreeBuilder`]** let you create a new root node and its descendants at
/// once. For detail, see the documentation for [`TreeBuilder`].
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
pub struct Forest<T> {
    /// Hierarchy.
    hierarchy: Hierarchy,
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
impl<T> Forest<T> {
    /// Creates a new empty forest.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::Forest;
    ///
    /// let mut forest = Forest::new();
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
impl<T> Forest<T> {
    /// Returns true if the node exists and is not yet removed.
    #[must_use]
    fn is_alive(&self, id: NodeId) -> bool {
        self.data
            .get(id.get())
            .map_or(false, |entry| entry.is_some())
    }

    /// Returns a [proxy object][`Node`] to the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::Forest;
    ///
    /// let mut forest = Forest::new();
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
    pub fn node(&self, id: NodeId) -> Option<Node<'_, T>> {
        Node::new(self, id)
    }

    /// Returns a [proxy object][`NodeMut`] to the mutable node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{AdoptAs, Forest};
    ///
    /// let mut forest = Forest::new();
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
    pub fn node_mut(&mut self, id: NodeId) -> Option<NodeMut<'_, T>> {
        NodeMut::new(self, id)
    }

    /// Returns a reference to the data associated to the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::Forest;
    ///
    /// let mut forest = Forest::new();
    /// let id = forest.create_root(42);
    ///
    /// assert_eq!(forest.data(id).copied(), Some(42));
    /// ```
    #[inline]
    #[must_use]
    pub fn data(&self, id: NodeId) -> Option<&T> {
        self.data.get(id.get()).and_then(|entry| entry.as_ref())
    }

    /// Returns a reference to the data associated to the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::Forest;
    ///
    /// let mut forest = Forest::new();
    /// let id = forest.create_root(42);
    /// assert_eq!(forest.data(id).copied(), Some(42));
    ///
    /// *forest.data_mut(id).expect("should never fail: node exists") = 314;
    ///
    /// assert_eq!(forest.data(id).copied(), Some(314));
    /// ```
    #[inline]
    #[must_use]
    pub fn data_mut(&mut self, id: NodeId) -> Option<&mut T> {
        self.data.get_mut(id.get()).and_then(|entry| entry.as_mut())
    }

    /// Returns a reference to the neighbors data associated to the node.
    #[inline]
    #[must_use]
    fn neighbors(&self, id: NodeId) -> Option<&Neighbors> {
        self.hierarchy.neighbors(id)
    }
}

/// Node creation and/or insertion.
impl<T> Forest<T> {
    /// Creates a new root node.
    ///
    /// # Panics
    ///
    /// Panics if the node ID overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::Forest;
    ///
    /// let mut forest = Forest::new();
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
    /// use treena::dynamic::Forest;
    ///
    /// let mut forest = Forest::new();
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
    pub fn create_root(&mut self, data: T) -> NodeId {
        let new_id = self.hierarchy.create_root();
        assert_eq!(
            self.data.len(),
            new_id.get(),
            "[consistency] node ID must be able to be used as an index for the vec"
        );
        self.data.push(Some(data));

        new_id
    }

    /// Creates a node and inserts it to the target position.
    ///
    /// Returns the node ID of the newly created node.
    ///
    /// To see how [`InsertAs`] works, see [`insert`][`Self::insert`] method.
    ///
    /// # Panics
    ///
    /// Panics if the node (the anchor of the destination) is not alive.
    #[inline]
    pub fn create_insert(&mut self, data: T, dest: InsertAs) -> NodeId {
        let new_id = self.create_root(data);
        self.insert(new_id, dest)
            .expect("[consistency] newly created node is independent from the destination");

        new_id
    }
}

/// Detaching and insertion.
impl<T> Forest<T> {
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
    /// # #[cfg(feature = "debug-print")] {
    /// use treena::dynamic::InsertAs;
    ///
    /// # use treena::dynamic::{Forest, TreeBuilder};
    /// # let mut forest = Forest::new();
    /// # let mut builder = TreeBuilder::new(&mut forest, "root");
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
    /// // NOTE: `.debug_print()` requires `debug-print` feature to be enabled.
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
    /// # }
    /// ```
    ///
    /// [`InsertAs::PreviousSiblingOf`] inserts the node as the previous sibling
    /// of some other node.
    ///
    /// ```
    /// # #[cfg(feature = "debug-print")] {
    /// use treena::dynamic::InsertAs;
    ///
    /// # use treena::dynamic::{Forest, TreeBuilder};
    /// # let mut forest = Forest::new();
    /// # let mut builder = TreeBuilder::new(&mut forest, "root");
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
    /// // NOTE: `.debug_print()` requires `debug-print` feature to be enabled.
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
    /// # }
    /// ```
    ///
    /// [`InsertAs::FirstChildOf`] inserts the node as the first child of some
    /// other node.
    ///
    /// ```
    /// # #[cfg(feature = "debug-print")] {
    /// use treena::dynamic::InsertAs;
    ///
    /// # use treena::dynamic::{Forest, TreeBuilder};
    /// # let mut forest = Forest::new();
    /// # let mut builder = TreeBuilder::new(&mut forest, "root");
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
    /// // NOTE: `.debug_print()` requires `debug-print` feature to be enabled.
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
    /// # }
    /// ```
    ///
    /// [`InsertAs::LastChildOf`] inserts the node as the last child of some
    /// other node.
    ///
    /// ```
    /// # #[cfg(feature = "debug-print")] {
    /// use treena::dynamic::InsertAs;
    ///
    /// # use treena::dynamic::{Forest, TreeBuilder};
    /// # let mut forest = Forest::new();
    /// # let mut builder = TreeBuilder::new(&mut forest, "root");
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
    /// // NOTE: `.debug_print()` requires `debug-print` feature to be enabled.
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
    /// # }
    /// ```
    #[inline]
    pub fn insert(&mut self, node: NodeId, dest: InsertAs) -> Result<(), StructureError> {
        self.hierarchy.insert(node, dest)
    }
}

/// Detaching and/or removal.
impl<T> Forest<T> {
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
    /// # #[cfg(feature = "debug-print")] {
    /// # use treena::dynamic::{Forest, TreeBuilder};
    /// # let mut forest = Forest::new();
    /// # let mut builder = TreeBuilder::new(&mut forest, "root");
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
    /// // NOTE: `.debug_print()` requires `debug-print` feature to be enabled.
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
    /// # }
    /// ```
    #[inline]
    pub fn detach(&mut self, node: NodeId) {
        self.hierarchy.detach(node);
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
    /// # #[cfg(feature = "debug-print")] {
    /// # use treena::dynamic::{Forest, TreeBuilder};
    /// # let mut forest = Forest::new();
    /// # let mut builder = TreeBuilder::new(&mut forest, "root");
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
    /// // NOTE: `.debug_print()` requires `debug-print` feature to be enabled.
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
    /// # }
    /// ```
    #[inline]
    pub fn detach_single(&mut self, node: NodeId) -> Result<(), StructureError> {
        self.hierarchy.detach_single(node)
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
    /// # #[cfg(feature = "debug-print")] {
    /// # use treena::dynamic::{Forest, TreeBuilder};
    /// # let mut forest = Forest::new();
    /// # let mut builder = TreeBuilder::new(&mut forest, "root");
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
    /// // NOTE: `.debug_print()` requires `debug-print` feature to be enabled.
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
    /// # }
    /// ```
    pub fn remove_hooked_panic_safe<F: FnMut(T)>(&mut self, node: NodeId, mut f: F) {
        if !self.is_alive(node) {
            return;
        }
        self.detach(node);

        let mut traverser = SafeModeDepthFirstTraverser::new(node, &self.hierarchy);
        while let Some(ev) = traverser.next(&self.hierarchy) {
            let id = match ev {
                DftEvent::Open(_) => continue,
                DftEvent::Close(id) => id,
            };

            // Detach the leaf node.
            debug_assert!(
                self.neighbors(id)
                    .expect("[consistency] the current node must be alive here")
                    .first_child()
                    .is_none(),
                "[consistency] the node must be the leaf"
            );
            self.detach(id);
            let nbs = self
                .hierarchy
                .neighbors_mut(id)
                .expect("[consistency] the current node must be alive here");
            debug_assert!(
                nbs.is_alone(),
                "[consistency] the detached leaf node must be alone"
            );
            nbs.make_removed();
            let data = self.data[id.get()]
                .take()
                .expect("[consistency] the node must have an associated data");
            f(data);
        }
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
    /// # #[cfg(feature = "debug-print")] {
    /// # use treena::dynamic::{Forest, TreeBuilder};
    /// # let mut forest = Forest::new();
    /// # let mut builder = TreeBuilder::new(&mut forest, "root");
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
    /// // NOTE: `.debug_print()` requires `debug-print` feature to be enabled.
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
    /// # }
    /// ```
    pub fn remove_hooked<F: FnMut(T)>(&mut self, node: NodeId, mut f: F) {
        if !self.is_alive(node) {
            return;
        }
        self.detach(node);

        let mut traverser = SafeModeDepthFirstTraverser::new(node, &self.hierarchy);
        while let Some(ev) = traverser.next(&self.hierarchy) {
            let id = match ev {
                DftEvent::Open(_) => continue,
                DftEvent::Close(id) => id,
            };

            // Break the node. The tree will be temporarily inconsistent.
            let nbs = self
                .hierarchy
                .neighbors_mut(id)
                .expect("[consistency] the current node must be alive here");
            nbs.force_make_removed();
            let data = self.data[id.get()]
                .take()
                .expect("[consistency] the node must have an associated data");
            f(data);
        }
        // At this point, all nodes under the `node` are removed.
        // Now the forest must be totally consistent.
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
    /// # #[cfg(feature = "debug-print")] {
    /// # use treena::dynamic::{Forest, TreeBuilder};
    /// # let mut forest = Forest::new();
    /// # let mut builder = TreeBuilder::new(&mut forest, "root");
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
    /// // NOTE: `.debug_print()` requires `debug-print` feature to be enabled.
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
    /// # }
    /// ```
    #[inline]
    pub fn remove(&mut self, node: NodeId) {
        self.remove_hooked(node, drop);
    }
}

/// Iteration.
impl<T> Forest<T> {
    /// Returns a depth-first traversal iterator of a subtree.
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{DftEvent, Forest, InsertAs};
    ///
    /// let mut forest = Forest::new();
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
    pub fn depth_first_traverse(&self, node: NodeId) -> traverse::DepthFirstTraverse<'_, T> {
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
    /// use treena::dynamic::{DftEvent, Forest, InsertAs};
    ///
    /// let mut forest = Forest::new();
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
    /// use treena::dynamic::{DftEvent, Forest, InsertAs};
    ///
    /// let mut forest = Forest::new();
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
        node: NodeId,
        max_depth: Option<usize>,
    ) -> traverse::ShallowDepthFirstTraverse<'_, T> {
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
    /// use treena::dynamic::{Forest, InsertAs, TreeBuilder};
    ///
    /// let mut forest = Forest::new();
    /// let root = TreeBuilder::new(&mut forest, "root")
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
    pub fn breadth_first_traverse(&self, node: NodeId) -> traverse::BreadthFirstTraverse<'_, T> {
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
    /// use treena::dynamic::{Forest, InsertAs, TreeBuilder};
    ///
    /// let mut forest = Forest::new();
    /// let root = TreeBuilder::new(&mut forest, "root")
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
        node: NodeId,
    ) -> traverse::AllocatingBreadthFirstTraverse<'_, T> {
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
    /// use treena::dynamic::{Forest, InsertAs};
    ///
    /// let mut forest = Forest::new();
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
    pub fn ancestors(&self, node: NodeId) -> traverse::Ancestors<'_, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .ancestors()
    }

    /// Returns an iterator of ancestors, including this node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, InsertAs};
    ///
    /// let mut forest = Forest::new();
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
    pub fn ancestors_or_self(&self, node: NodeId) -> traverse::Ancestors<'_, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .ancestors_or_self()
    }

    /// Returns an iterator of children.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{DftEvent, Forest, InsertAs};
    ///
    /// let mut forest = Forest::new();
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
    pub fn children(&self, node: NodeId) -> traverse::Siblings<'_, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .children()
    }

    /// Returns an iterator of the following siblings, excluding this node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, InsertAs};
    ///
    /// let mut forest = Forest::new();
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
    pub fn following_siblings(&self, node: NodeId) -> traverse::Siblings<'_, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .following_siblings()
    }

    /// Returns an iterator of the following siblings, including this node.
    ///
    /// # Examples
    ///
    /// ```
    /// use treena::dynamic::{Forest, InsertAs};
    ///
    /// let mut forest = Forest::new();
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
    pub fn following_siblings_or_self(&self, node: NodeId) -> traverse::Siblings<'_, T> {
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
    /// use treena::dynamic::{Forest, InsertAs};
    ///
    /// let mut forest = Forest::new();
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
    pub fn preceding_siblings(&self, node: NodeId) -> traverse::Siblings<'_, T> {
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
    /// use treena::dynamic::{Forest, InsertAs};
    ///
    /// let mut forest = Forest::new();
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
    pub fn preceding_siblings_or_self(&self, node: NodeId) -> traverse::Siblings<'_, T> {
        self.node(node)
            .expect("[precondition] node must be alive")
            .preceding_siblings_or_self()
    }
}

/// Tree cloning.
impl<T: Clone> Forest<T> {
    /// Clones a subtree as a new tree in the forest, and returns the new root ID.
    ///
    /// # Panics
    ///
    /// Panics if the node (including descendants) are not alive.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "debug-print")] {
    /// # use treena::dynamic::{Forest, TreeBuilder};
    /// # let mut forest = Forest::new();
    /// # let mut builder = TreeBuilder::new(&mut forest, "root");
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
    /// // NOTE: `.debug_print()` requires `debug-print` feature to be enabled.
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
    /// # }
    /// ```
    pub fn clone_local_tree(&mut self, src_id: NodeId) -> NodeId {
        let root_data = self
            .data(src_id)
            .expect("[consistency] the node must be alive")
            .clone();
        let root_id = self.create_root(root_data);
        let mut current_dest = root_id;
        let mut traverser = SafeModeDepthFirstTraverser::new(src_id, &self.hierarchy);

        // Skip the open event of the root node.
        let _ = traverser.next(&self.hierarchy);

        while let Some(ev) = traverser.next(&self.hierarchy) {
            match ev {
                DftEvent::Open(src_id) => {
                    let data = self
                        .data(src_id)
                        .expect("[consistency] the node being traversed must be alive")
                        .clone();
                    current_dest = self.create_insert(data, InsertAs::LastChildOf(current_dest));
                }
                DftEvent::Close(_) => {
                    let parent = self
                        .node(current_dest)
                        .expect("[consistency] the node being created must be alive")
                        .parent_id();
                    current_dest = match parent {
                        Some(id) => id,
                        None => {
                            assert_eq!(
                                current_dest, root_id,
                                "[consistency] current node must be the root if it has no parent"
                            );
                            break;
                        }
                    }
                }
            }
        }
        assert_eq!(
            current_dest, root_id,
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
    /// # #[cfg(feature = "debug-print")] {
    /// # use treena::dynamic::{Forest, TreeBuilder};
    /// # let mut forest_src = Forest::new();
    /// # let mut builder = TreeBuilder::new(&mut forest_src, "root");
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
    /// // NOTE: `.debug_print()` requires `debug-print` feature to be enabled.
    /// assert_eq!(forest_src.debug_print(root).to_string(), before);
    ///
    /// // Destination forest.
    /// let mut forest_dest = Forest::new();
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
    /// # }
    /// ```
    pub fn clone_foreign_tree(&mut self, src_root: Node<'_, T>) -> NodeId {
        use crate::dynamic::forest::traverse::DftEvent;

        let mut events = src_root.depth_first_traverse();
        let root_data = match events.next() {
            None => unreachable!(
                "[validity] iterator must emit at least two events since it has the root node"
            ),
            Some(DftEvent::Open(node)) => node.data().clone(),
            Some(DftEvent::Close(_)) => {
                unreachable!("[validity] `DepthFirstTraverse` must emit the open event first")
            }
        };
        let mut builder = TreeBuilder::new(self, root_data);

        for ev in events {
            match ev {
                DftEvent::Open(node) => {
                    let data = node.data().clone();
                    builder.child(data);
                }
                DftEvent::Close(_) => {
                    // When `builder.try_parent().is_none()` is true, it
                    // means that the node being closed is the root node of the
                    // new tree. It is not an error and no action needed here,
                    // since no more events will be provided from `events`.
                    let _ = builder.try_parent();
                }
            }
        }

        builder.root_id()
    }
}

/// Debug printing.
#[cfg(feature = "debug-print")]
impl<T> Forest<T> {
    /// Returns the pretty-printable proxy object to the node and descendants.
    ///
    /// This requires `debug-print` feature to be enabled.
    #[cfg(feature = "debug-print")]
    #[cfg_attr(feature = "docsrs", doc(cfg(feature = "debug-print")))]
    pub fn debug_print(&self, id: NodeId) -> debug_print::DebugPrint<'_, T> {
        let node = self
            .node(id)
            .expect("[precondition] the node must be alive");
        debug_print::DebugPrint::new(node)
    }
}

impl<T> Default for Forest<T> {
    fn default() -> Self {
        Self {
            hierarchy: Default::default(),
            data: Default::default(),
        }
    }
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
