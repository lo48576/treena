//! Forest.

use crate::dynamic::hierarchy::Hierarchy;
use crate::dynamic::id::NodeId;

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
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns a reference to the data associated to the node.
    #[inline]
    #[must_use]
    pub fn data(&self, id: NodeId) -> Option<&T> {
        self.data.get(id.get()).and_then(|entry| entry.as_ref())
    }

    /// Returns a reference to the data associated to the node.
    #[inline]
    #[must_use]
    pub fn data_mut(&mut self, id: NodeId) -> Option<&mut T> {
        self.data.get_mut(id.get()).and_then(|entry| entry.as_mut())
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
