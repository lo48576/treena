//! Forest.

mod node;
pub mod traverse;

use crate::dynamic::hierarchy::{Hierarchy, Neighbors};
use crate::dynamic::id::NodeId;

pub use self::node::Node;

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
}

impl<T> Default for Forest<T> {
    fn default() -> Self {
        Self {
            hierarchy: Default::default(),
            data: Default::default(),
        }
    }
}
