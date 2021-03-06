//! Chain-style tree and forest builder.

use crate::dynamic::forest::Forest;
use crate::dynamic::{InsertAs, NodeId};

/// Chain-style tree builder.
///
/// `ChainTreeBuilder` remembers "the current node".
///
/// * [`ChainTreeBuilder::child()`][`ChainTreeBuilder::child`] creates a new child node
///   (as the last child) to the current node.
/// * [`ChainTreeBuilder::sibling()`][`ChainTreeBuilder::sibling`] creates a new next
///   sibling of the current node.
/// * [`ChainTreeBuilder::parent()`][`ChainTreeBuilder::parent`] makes the parent the new current node.
///
/// [`ChainTreeBuilder::root_id()`][`ChainTreeBuilder::root_id`] returns the root node ID,
/// and [`ChainTreeBuilder::current_id()`][`ChainTreeBuilder::current_id`] returns the
/// node ID of the current node.
///
/// # Examples
///
/// Builder can be reused, but note that it remembers the root and the current node.
///
/// ```
/// # use treena::dynamic::DftEvent;
/// use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
///
/// let mut forest: Forest<NodeIdUsize, &'static str> = Forest::new();
/// let mut builder = ChainTreeBuilder::new(&mut forest, "root");
/// builder
///     .child("0")
///     .child("0-0")
///     .sibling("0-1")
///     .parent()
///     .sibling("1")
///     .child("1-0");
///
/// // Tree:
/// //  root
/// //  |-- 0
/// //  |   |-- 0-0
/// //  |   `-- 0-1
/// //  `-- 1
/// //      `-- 1-0 (<-- current)
///
/// builder
///     .parent()
///     .child("1-1")
///     .parent()
///     .sibling("2");
///
/// // Tree:
/// //  root
/// //  |-- 0
/// //  |   |-- 0-0
/// //  |   `-- 0-1
/// //  |-- 1
/// //  |   |-- 1-0
/// //  |   `-- 1-1
/// //  `-- 2 (<-- current)
/// #
/// # let root = builder.root_id();
/// # assert_eq!(
/// #     forest.node(root)
/// #         .expect("should never fail: the created node must be alive")
/// #         .depth_first_traverse()
/// #         .map(|ev| ev.map(|node| *node.data()))
/// #         .collect::<Vec<_>>(),
/// #     &[
/// #         DftEvent::Open("root"),
/// #         DftEvent::Open("0"),
/// #         DftEvent::Open("0-0"),
/// #         DftEvent::Close("0-0"),
/// #         DftEvent::Open("0-1"),
/// #         DftEvent::Close("0-1"),
/// #         DftEvent::Close("0"),
/// #         DftEvent::Open("1"),
/// #         DftEvent::Open("1-0"),
/// #         DftEvent::Close("1-0"),
/// #         DftEvent::Open("1-1"),
/// #         DftEvent::Close("1-1"),
/// #         DftEvent::Close("1"),
/// #         DftEvent::Open("2"),
/// #         DftEvent::Close("2"),
/// #         DftEvent::Close("root"),
/// #     ]
/// # );
/// ```
///
/// You can create a tree and get the root node ID at once.
///
/// ```
/// # use treena::dynamic::DftEvent;
/// use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
///
/// let mut forest = Forest::<NodeIdUsize, _>::new();
/// let root = ChainTreeBuilder::new(&mut forest, "root")
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
/// // Tree:
/// //  root
/// //  |-- 0
/// //  |   |-- 0-0
/// //  |   |   `-- 0-0-0
/// //  |   `-- 0-1
/// //  |-- 1
/// //  |-- 2
/// //  |   `-- 2-0
/// //  `-- 3
/// #
/// # assert_eq!(
/// #     forest.node(root)
/// #         .expect("should never fail: the created node must be alive")
/// #         .depth_first_traverse()
/// #         .map(|ev| ev.map(|node| *node.data()))
/// #         .collect::<Vec<_>>(),
/// #     &[
/// #         DftEvent::Open("root"),
/// #         DftEvent::Open("0"),
/// #         DftEvent::Open("0-0"),
/// #         DftEvent::Open("0-0-0"),
/// #         DftEvent::Close("0-0-0"),
/// #         DftEvent::Close("0-0"),
/// #         DftEvent::Open("0-1"),
/// #         DftEvent::Close("0-1"),
/// #         DftEvent::Close("0"),
/// #         DftEvent::Open("1"),
/// #         DftEvent::Close("1"),
/// #         DftEvent::Open("2"),
/// #         DftEvent::Open("2-0"),
/// #         DftEvent::Close("2-0"),
/// #         DftEvent::Close("2"),
/// #         DftEvent::Open("3"),
/// #         DftEvent::Close("3"),
/// #         DftEvent::Close("root"),
/// #     ]
/// # );
/// ```
#[derive(Debug)]
pub struct ChainTreeBuilder<'a, Id: NodeId, T> {
    /// Target forest.
    forest: &'a mut Forest<Id, T>,
    /// Node ID of the root node.
    root: Id,
    /// Current node.
    current: Id,
}

impl<'a, Id: NodeId, T> ChainTreeBuilder<'a, Id, T> {
    /// Creates a root node and the tree builder for the root node.
    pub fn new(forest: &'a mut Forest<Id, T>, root_data: T) -> Self {
        let root = forest.create_root(root_data);
        Self {
            forest,
            root,
            current: root,
        }
    }

    /// Returns a reference to the forest.
    #[inline]
    #[must_use]
    pub fn forest(&self) -> &Forest<Id, T> {
        self.forest
    }

    /// Returns a mutable reference to the forest.
    #[inline]
    #[must_use]
    pub fn forest_mut(&mut self) -> &mut Forest<Id, T> {
        self.forest
    }

    /// Returns the node ID of the root node.
    #[inline]
    #[must_use]
    pub fn root_id(&self) -> Id {
        self.root
    }

    /// Returns the node ID of the current node.
    #[inline]
    #[must_use]
    pub fn current_id(&self) -> Id {
        self.current
    }

    /// Appends a child node to the current node, and changes the current node to it.
    pub fn child(&mut self, data: T) -> &mut Self {
        let new = self
            .forest
            .create_insert(data, InsertAs::LastChildOf(self.current));
        self.current = new;
        self
    }

    /// Adds a next sibling node to the current node, and changes the current node to it.
    pub fn sibling(&mut self, data: T) -> &mut Self {
        let new = self
            .forest
            .create_insert(data, InsertAs::NextSiblingOf(self.current));
        self.current = new;
        self
    }

    /// Tries to change the current node to the parent of the current node.
    pub fn try_parent(&mut self) -> Option<&mut Self> {
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
    pub fn parent(&mut self) -> &mut Self {
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
