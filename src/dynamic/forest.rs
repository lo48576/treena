//! Forest.

mod builder;
#[cfg(any(doctest, feature = "debug-print"))]
pub mod debug_print;
mod node;
pub mod traverse;

use core::fmt;

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
    /// use treena::dynamic::Forest;
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
    /// node.create_last_child(141421356);
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

    /// Detaches the tree from neighbors.
    ///
    /// Tree structure under the given node will be preserved.
    /// The detached node will become a root node.
    ///
    /// If you want to detach not subtree but single node, use
    /// [`detach_single`][`Self::detach_single`] method.
    ///
    /// ```text
    /// Before `detach`:
    ///
    /// root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2
    ///
    /// After `detach`:
    ///
    /// root
    /// |-- 0
    /// `-- 2
    ///
    /// 1
    /// |-- 1-0
    /// |-- 1-1
    /// `-- 1-2
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
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
    /// ```text
    /// Before `detach_single`:
    ///
    /// root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2
    ///
    /// After `detach_single`:
    ///
    /// root
    /// |-- 0
    /// |-- 1-0
    /// |-- 1-1
    /// |-- 1-2
    /// `-- 2
    ///
    /// 1
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`StructureError::SiblingsWithoutParent`] when the node has
    /// multiple children but has no parent.
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
    #[inline]
    pub fn detach_single(&mut self, node: NodeId) -> Result<(), StructureError> {
        self.hierarchy.detach_single(node)
    }

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
    #[inline]
    pub fn insert(&mut self, node: NodeId, dest: InsertAs) -> Result<(), StructureError> {
        self.hierarchy.insert(node, dest)
    }

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
