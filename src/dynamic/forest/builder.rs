//! Tree and forest builder.

use crate::dynamic::forest::Forest;
use crate::dynamic::{InsertAs, NodeId};

/// Tree builder.
///
/// # Examples
///
/// ```
/// use treena::dynamic::forest::{Forest, TreeBuilder};
/// use treena::dynamic::forest::traverse::DftEvent;
///
/// let mut forest = Forest::new();
/// let root = TreeBuilder::new(&mut forest, "root")
///     .child("0")
///     .child("0-0")
///     .child("0-0-0")
///     .parent()
///     .sibling("0-1")
///     .parent()
///     .sibling("1")
///     .sibling("2")
///     .child("2-0")
///     .parent()
///     .sibling("3")
///     .root_id();
///
/// assert_eq!(
///     forest.node(root)
///         .expect("should never fail: the created node must be alive")
///         .depth_first_traverse()
///         .map(|ev| ev.map(|node| *node.data()))
///         .collect::<Vec<_>>(),
///     &[
///         DftEvent::Open("root"),
///         DftEvent::Open("0"),
///         DftEvent::Open("0-0"),
///         DftEvent::Open("0-0-0"),
///         DftEvent::Close("0-0-0"),
///         DftEvent::Close("0-0"),
///         DftEvent::Open("0-1"),
///         DftEvent::Close("0-1"),
///         DftEvent::Close("0"),
///         DftEvent::Open("1"),
///         DftEvent::Close("1"),
///         DftEvent::Open("2"),
///         DftEvent::Open("2-0"),
///         DftEvent::Close("2-0"),
///         DftEvent::Close("2"),
///         DftEvent::Open("3"),
///         DftEvent::Close("3"),
///         DftEvent::Close("root"),
///     ]
/// );
/// ```
#[derive(Debug)]
pub struct TreeBuilder<'a, T> {
    /// Target forest.
    forest: &'a mut Forest<T>,
    /// Node ID of the root node.
    root: NodeId,
    /// Current node.
    current: NodeId,
}

impl<'a, T: Clone> TreeBuilder<'a, T> {
    /// Creates a root node and the tree builder for the root node.
    pub fn new(forest: &'a mut Forest<T>, root_data: T) -> Self {
        let root = forest.create_root(root_data);
        Self {
            forest,
            root,
            current: root,
        }
    }

    /// Returns the node ID of the root node.
    #[inline]
    #[must_use]
    pub fn root_id(&self) -> NodeId {
        self.root
    }

    /// Returns the node ID of the current node.
    #[inline]
    #[must_use]
    pub fn current_id(&self) -> NodeId {
        self.current
    }

    /// Appends a child node to the current node, and changes the current node to it.
    pub fn child(mut self, data: T) -> Self {
        let new = self
            .forest
            .create_insert(data, InsertAs::LastChildOf(self.current));
        self.current = new;
        self
    }

    /// Adds a next sibling node to the current node, and changes the current node to it.
    pub fn sibling(mut self, data: T) -> Self {
        let new = self
            .forest
            .create_insert(data, InsertAs::NextSiblingOf(self.current));
        self.current = new;
        self
    }

    /// Tries to change the current node to the parent of the current node.
    pub fn try_parent(mut self) -> Option<Self> {
        let parent = self
            .forest
            .node(self.current)
            .expect("[consistency] nodes in the tree must be alive")
            .parent_id()?;
        self.current = parent;
        Some(self)
    }

    /// Changes the current node to the parent of the current node.
    ///
    /// # Panics
    ///
    /// Panics if the current node is the root of a tree.
    pub fn parent(mut self) -> Self {
        let parent = self
            .forest
            .node(self.current)
            .expect("[consistency] nodes in the tree must be alive")
            .parent_id()
            .expect("[precondition] the current node should not be the root");
        self.current = parent;
        self
    }
}