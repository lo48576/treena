//! Forest.

mod builder;
#[cfg(any(feature = "debug-print"))]
pub mod debug_print;
mod node;
pub mod traverse;

use core::fmt;

use alloc::vec::Vec;

use crate::dynamic::hierarchy::traverse::{DftEvent, SafeModeDepthFirstTraverser};
use crate::dynamic::hierarchy::{Hierarchy, Neighbors};
use crate::dynamic::{InsertAs, NodeId};

pub use self::builder::TreeBuilder;
pub use self::node::{Node, NodeMut};

/// Forest.
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
impl<T: Clone> Forest<T> {
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
    /// # use treena::dynamic::forest::{Forest, TreeBuilder};
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
    /// # use treena::dynamic::forest::{Forest, TreeBuilder};
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
    /// # use treena::dynamic::forest::{Forest, TreeBuilder};
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
    /// # use treena::dynamic::forest::{Forest, TreeBuilder};
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
    /// # use treena::dynamic::forest::{Forest, TreeBuilder};
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
    /// # use treena::dynamic::forest::{Forest, TreeBuilder};
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
    /// # use treena::dynamic::forest::{Forest, TreeBuilder};
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

        let mut traverser = SafeModeDepthFirstTraverser::new(node);
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
    /// # use treena::dynamic::forest::{Forest, TreeBuilder};
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

        let mut traverser = SafeModeDepthFirstTraverser::new(node);
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
    /// # use treena::dynamic::forest::{Forest, TreeBuilder};
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
