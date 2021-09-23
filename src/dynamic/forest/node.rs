//! Node.

#[cfg(feature = "debug-print")]
use crate::dynamic::forest::debug_print::DebugPrint;
use crate::dynamic::forest::traverse::{Ancestors, DepthFirstTraverse, Siblings};
use crate::dynamic::forest::StructureError;
use crate::dynamic::{AdoptAs, Forest, NodeId};

/// Immutable reference to a node.
///
/// This type guarantees that the node ID must be present in the internal
/// storage of the tree and must not be removed yet.
#[derive(Debug)]
pub struct Node<'a, T> {
    /// Forest.
    forest: &'a Forest<T>,
    /// Node ID.
    id: NodeId,
}

/// Node creation.
impl<'a, T> Node<'a, T> {
    /// Creates a new `Node` object.
    #[must_use]
    pub(super) fn new(forest: &'a Forest<T>, id: NodeId) -> Option<Self> {
        if !forest.is_alive(id) {
            return None;
        }
        Some(Self { forest, id })
    }
}

/// Data and property access.
impl<'a, T> Node<'a, T> {
    /// Returns a reference to the forest.
    #[inline]
    #[must_use]
    pub fn forest(&self) -> &'a Forest<T> {
        self.forest
    }

    /// Returns the node ID.
    #[inline]
    #[must_use]
    pub fn id(&self) -> NodeId {
        self.id
    }

    /// Returns a reference to the data associated to the node.
    #[inline]
    #[must_use]
    pub fn data(&self) -> &T {
        self.forest
            .data(self.id)
            .expect("[validity] the node has been checked to be alive")
    }
}

/// Neighbors access.
impl<'a, T> Node<'a, T> {
    /// Returns the node ID of the parent.
    #[must_use]
    pub fn parent_id(&self) -> Option<NodeId> {
        self.forest
            .neighbors(self.id)
            .expect("[validity] the node has been checked to be alive")
            .parent()
    }

    /// Returns the node ID of the next sibling.
    #[must_use]
    pub fn next_sibling_id(&self) -> Option<NodeId> {
        self.forest
            .neighbors(self.id)
            .expect("[validity] the node has been checked to be alive")
            .next_sibling()
    }

    /// Returns the node ID of the previous sibling.
    #[must_use]
    pub fn prev_sibling_id(&self) -> Option<NodeId> {
        self.forest
            .neighbors(self.id)
            .expect("[validity] the node has been checked to be alive")
            .prev_sibling(&self.forest.hierarchy)
    }

    /// Returns the node ID of the first child.
    #[must_use]
    pub fn first_child_id(&self) -> Option<NodeId> {
        self.forest
            .neighbors(self.id)
            .expect("[validity] the node has been checked to be alive")
            .first_child()
    }

    /// Returns the node ID of the last child.
    #[must_use]
    pub fn last_child_id(&self) -> Option<NodeId> {
        self.forest
            .neighbors(self.id)
            .expect("[validity] the node has been checked to be alive")
            .last_child(&self.forest.hierarchy)
    }

    /// Returns the node IDs of the first child and the last child.
    #[must_use]
    pub fn first_last_child_id(&self) -> Option<(NodeId, NodeId)> {
        self.forest
            .neighbors(self.id)
            .expect("[validity] the node has been checked to be alive")
            .first_last_child(&self.forest.hierarchy)
    }

    /// Returns the parent node.
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        self.parent_id()
            .map(|id| Self::new(self.forest, id).expect("[consistency] the parent must be alive"))
    }

    /// Returns the next sibling node.
    #[must_use]
    pub fn next_sibling(&self) -> Option<Self> {
        self.next_sibling_id().map(|id| {
            Self::new(self.forest, id).expect("[consistency] the next sibling must be alive")
        })
    }

    /// Returns the previous sibling node.
    #[must_use]
    pub fn prev_sibling(&self) -> Option<Self> {
        self.prev_sibling_id().map(|id| {
            Self::new(self.forest, id).expect("[consistency] the previous sibling must be alive")
        })
    }

    /// Returns the first child node.
    #[must_use]
    pub fn first_child(&self) -> Option<Self> {
        self.first_child_id().map(|id| {
            Self::new(self.forest, id).expect("[consistency] the first child must be alive")
        })
    }

    /// Returns the last child node.
    #[must_use]
    pub fn last_child(&self) -> Option<Self> {
        self.last_child_id().map(|id| {
            Self::new(self.forest, id).expect("[consistency] the last child must be alive")
        })
    }

    /// Returns the first child and the last child.
    #[must_use]
    pub fn first_last_child(&self) -> Option<(Self, Self)> {
        self.forest
            .neighbors(self.id)
            .expect("[validity] the node has been checked to be alive")
            .first_last_child(&self.forest.hierarchy)
            .map(|(first, last)| {
                (
                    Self::new(self.forest, first)
                        .expect("[consistency] the first child must be alive"),
                    Self::new(self.forest, last)
                        .expect("[consistency] the last child must be alive"),
                )
            })
    }
}

/// Iteration.
impl<'a, T> Node<'a, T> {
    /// Returns a depth-first traversal iterator of a subtree.
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
    /// let node = forest.node(root).expect("should never fail: node exists");
    /// assert_eq!(
    ///     node
    ///         .depth_first_traverse()
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
    pub fn depth_first_traverse(&self) -> DepthFirstTraverse<'a, T> {
        DepthFirstTraverse::with_toplevel(self)
    }

    /// Returns an iterator of ancestors, excluding this node.
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
    /// let node = forest.node(child00).expect("should never fail: node exists");
    ///
    /// assert_eq!(
    ///     node.ancestors().map(|node| *node.data()).collect::<Vec<_>>(),
    ///     &["0", "root"]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn ancestors(&self) -> Ancestors<'a, T> {
        first_skipped(self.ancestors_or_self())
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
    /// let node = forest.node(child00).expect("should never fail: node exists");
    ///
    /// assert_eq!(
    ///     node.ancestors_or_self().map(|node| *node.data()).collect::<Vec<_>>(),
    ///     &["0-0", "0", "root"]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn ancestors_or_self(&self) -> Ancestors<'a, T> {
        Ancestors::with_start(self)
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
    /// let node = forest.node(root).expect("should never fail: node exists");
    ///
    /// assert_eq!(
    ///     node.children().map(|node| *node.data()).collect::<Vec<_>>(),
    ///     &["0", "1", "2"]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn children(&self) -> Siblings<'a, T> {
        Siblings::with_parent(self)
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
    /// let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// let child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    /// let child2 = forest.create_insert("2", InsertAs::LastChildOf(root));
    /// let node = forest.node(child1).expect("should never fail: node exists");
    ///
    /// assert_eq!(
    ///     node.following_siblings()
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["2"]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn following_siblings(&self) -> Siblings<'a, T> {
        first_skipped(self.following_siblings_or_self())
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
    /// let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// let child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    /// let child2 = forest.create_insert("2", InsertAs::LastChildOf(root));
    /// let node = forest.node(child1).expect("should never fail: node exists");
    ///
    /// assert_eq!(
    ///     node.following_siblings_or_self()
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["1", "2"]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn following_siblings_or_self(&self) -> Siblings<'a, T> {
        Siblings::with_first_sibling(self)
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
    /// let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// let child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    /// let child2 = forest.create_insert("2", InsertAs::LastChildOf(root));
    /// let child3 = forest.create_insert("3", InsertAs::LastChildOf(root));
    /// let node = forest.node(child2).expect("should never fail: node exists");
    ///
    /// assert_eq!(
    ///     node.preceding_siblings()
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["0", "1"]
    /// );
    /// assert_eq!(
    ///     node.preceding_siblings()
    ///         .rev() // REVERSED!
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["1", "0"],
    ///     "Use `.rev()` to iterate from the starting node to the first node"
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn preceding_siblings(&self) -> Siblings<'a, T> {
        last_skipped(self.preceding_siblings_or_self())
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
    /// let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    /// let child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    /// let child2 = forest.create_insert("2", InsertAs::LastChildOf(root));
    /// let child3 = forest.create_insert("3", InsertAs::LastChildOf(root));
    /// let node = forest.node(child2).expect("should never fail: node exists");
    ///
    /// assert_eq!(
    ///     node.preceding_siblings_or_self()
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["0", "1", "2"]
    /// );
    /// assert_eq!(
    ///     node.preceding_siblings_or_self()
    ///         .rev() // REVERSED!
    ///         .map(|node| *node.data())
    ///         .collect::<Vec<_>>(),
    ///     &["2", "1", "0"],
    ///     "Use `.rev()` to iterate from the starting node to the first node"
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn preceding_siblings_or_self(&self) -> Siblings<'a, T> {
        Siblings::with_last_sibling(self)
    }
}

/// Debug printing.
impl<'a, T> Node<'a, T> {
    /// Returns the pretty-printable proxy object to the node and descendants.
    ///
    /// This requires `debug-print` feature to be enabled.
    #[cfg(feature = "debug-print")]
    #[cfg_attr(feature = "docsrs", doc(cfg(feature = "debug-print")))]
    pub fn debug_print(&self) -> DebugPrint<'_, T> {
        DebugPrint::new(*self)
    }
}

impl<T> Clone for Node<'_, T> {
    fn clone(&self) -> Self {
        Self {
            forest: self.forest,
            id: self.id,
        }
    }
}

impl<T> Copy for Node<'_, T> {}

/// Mutable reference to a node.
///
/// This type guarantees that the node ID must be present in the internal
/// storage of the tree and must not be removed yet.
///
/// Values of this type are not intended to be long-lived, since it mutably
/// borrows the tree. Values must be transient in usual use cases.
/// In order to remember or track nodes for a while, use `NodeId` which does
/// not borrow the tree.
#[derive(Debug)]
pub struct NodeMut<'a, T> {
    /// Forest.
    forest: &'a mut Forest<T>,
    /// Node ID.
    id: NodeId,
}

/// Creation.
impl<'a, T> NodeMut<'a, T> {
    /// Creates a new `Node` object.
    #[must_use]
    pub(super) fn new(forest: &'a mut Forest<T>, id: NodeId) -> Option<Self> {
        if !forest.is_alive(id) {
            return None;
        }
        Some(Self { forest, id })
    }
}

/// Data and property access.
impl<'a, T> NodeMut<'a, T> {
    /// Returns the immutable reference to the node.
    pub fn node(&self) -> Node<'_, T> {
        Node::new(self.forest, self.id)
            .expect("[validity] the node must be already checked to be alive")
    }

    /// Converts the reference into the immutable reference to the node.
    pub fn into_node(self) -> Node<'a, T> {
        Node::new(self.forest, self.id)
            .expect("[validity] the node must be already checked to be alive")
    }

    /// Returns a reference to the forest.
    #[inline]
    #[must_use]
    pub fn forest(&self) -> &Forest<T> {
        self.forest
    }

    /// Returns the node ID.
    #[inline]
    #[must_use]
    pub fn id(&self) -> NodeId {
        self.id
    }

    /// Returns a reference to the data associated to the node.
    #[inline]
    #[must_use]
    pub fn data(&self) -> &T {
        self.forest
            .data(self.id)
            .expect("[validity] the node has been checked to be alive")
    }

    /// Returns a mutable reference to the data associated to the node.
    #[inline]
    #[must_use]
    pub fn data_mut(&mut self) -> &mut T {
        self.forest
            .data_mut(self.id)
            .expect("[validity] the node has been checked to be alive")
    }
}

/// Neighbor node creation.
impl<'a, T: Clone> NodeMut<'a, T> {
    /// Creates a node and inserts it to the target position.
    ///
    /// Returns the node ID of the newly created node.
    ///
    /// This method works in similar way as [`Forest::create_insert`].
    ///
    /// # Example
    ///
    /// Creating the first child by [`AdoptAs::FirstChild`]:
    ///
    /// ```
    /// # #[cfg(feature = "debug-print")] {
    /// use treena::dynamic::AdoptAs;
    ///
    /// # use treena::dynamic::{DftEvent, Forest, TreeBuilder};
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
    /// let mut node = forest.node_mut(child_1)
    ///     .expect("the node must be alive");
    /// // Create a new node.
    /// // Create a node "new" and insert it as the first child of the node "1".
    /// let new = node.create("new", AdoptAs::FirstChild);
    ///
    /// let after_create = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- new
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), after_create);
    /// # }
    /// ```
    ///
    /// Creating the last child by [`AdoptAs::LastChild`]:
    ///
    /// ```
    /// # #[cfg(feature = "debug-print")] {
    /// use treena::dynamic::AdoptAs;
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
    /// let mut node = forest.node_mut(child_1)
    ///     .expect("the node must be alive");
    /// // Create a new node.
    /// // Create a node "new" and insert it as the last child of the node "1".
    /// let new = node.create("new", AdoptAs::LastChild);
    ///
    /// let after_create = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   |-- 1-2
    /// |   `-- new
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), after_create);
    /// # }
    /// ```
    ///
    /// Creating the previous child by [`AdoptAs::PreviousSibling`]:
    ///
    /// ```
    /// # #[cfg(feature = "debug-print")] {
    /// use treena::dynamic::AdoptAs;
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
    /// let mut node = forest.node_mut(child_1)
    ///     .expect("the node must be alive");
    /// // Create a new node.
    /// // Create a node "new" and insert it as the previous sibling
    /// // of the node "1".
    /// let new = node.create("new", AdoptAs::PreviousSibling);
    ///
    /// let after_create = r#"root
    /// |-- 0
    /// |-- new
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), after_create);
    /// # }
    /// ```
    ///
    /// Creating the previous child by [`AdoptAs::PreviousSibling`]:
    ///
    /// ```
    /// # #[cfg(feature = "debug-print")] {
    /// use treena::dynamic::AdoptAs;
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
    /// let mut node = forest.node_mut(child_1)
    ///     .expect("the node must be alive");
    /// // Create a new node.
    /// // Create a node "new" and insert it as the next sibling
    /// // of the node "1".
    /// let new = node.create("new", AdoptAs::NextSibling);
    ///
    /// let after_create = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// |-- new
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), after_create);
    /// # }
    /// ```
    #[inline]
    pub fn create(&mut self, data: T, dest: AdoptAs) -> NodeId {
        self.forest
            .create_insert(data, dest.insert_with_anchor(self.id))
    }
}

/// Node insertion without creation.
impl<'a, T> NodeMut<'a, T> {
    /// Detaches the given node and inserts to the given place near `self` node.
    ///
    /// # Panics
    ///
    /// * Panics if `self` and `node` is the identical node.
    ///     + A node cannot be the neighbor of itself.
    /// * Panics if neither `self` nor `node` is alive.
    ///     + Removed or nonexistent nodes cannot be manipulated.
    /// * Panics if `self` does not have a parent while `dest` is
    ///   `PreviousSibling` or `NextSibling`.
    ///     + A node cannot have siblings without having a parent.
    ///
    /// # Examples
    ///
    /// [`AdoptAs::NextSibling`] inserts the given node as the next sibling of
    /// `self` node.
    ///
    /// ```
    /// # #[cfg(feature = "debug-print")] {
    /// use treena::dynamic::AdoptAs;
    ///
    /// # use treena::dynamic::{Forest, TreeBuilder};
    /// # let mut forest = Forest::new();
    /// # let mut builder = TreeBuilder::new(&mut forest, "root");
    /// # let child_1 = builder
    /// #     .child("0")
    /// #     .sibling("1")
    /// #     .current_id();
    /// # let child_1_1 = builder
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
    /// let mut node = forest.node_mut(child_1)
    ///     .expect("the node must be alive");
    /// // Adopt the node "1-1" as the next sibling of the node "1".
    /// node.adopt(child_1_1, AdoptAs::NextSibling);
    ///
    /// let after_adopt = r#"root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   `-- 1-2
    /// |-- 1-1
    /// |   |-- 1-1-0
    /// |   |-- 1-1-1
    /// |   `-- 1-1-2
    /// `-- 2"#;
    /// assert_eq!(forest.debug_print(root).to_string(), after_adopt);
    /// # }
    /// ```
    pub fn adopt(&mut self, node: NodeId, dest: AdoptAs) {
        self.try_adopt(node, dest)
            .expect("[precondition] structure to be made should be valid");
    }

    /// Tries to detach the given node and to insert to the given place near `self` node.
    ///
    /// # Errors
    ///
    /// * [`StructureError::AncestorDescendantLoop`]
    ///     + In case `dest` is `FirstChild` or `LastChild`, and
    ///       `self` and `node` are identical.
    /// * [`StructureError::UnorderableSiblings`]
    ///     + In case `dest` is `PreviousSibling` or `NextSibling`, and
    ///       `self` and `node` are identical.
    /// * [`StructureError::SiblingsWithoutParent`]
    ///     + In case `dest` is `PreviousSibling` or `NextSibling`, and
    ///       `self` does not have a parent.
    pub fn try_adopt(&mut self, node: NodeId, dest: AdoptAs) -> Result<(), StructureError> {
        self.forest
            .hierarchy
            .insert(node, dest.insert_with_anchor(self.id))
    }
}

/// Detach and/or removal.
impl<'a, T> NodeMut<'a, T> {
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
    /// let mut node = forest.node_mut(child_1)
    ///     .expect("the node must be alive");
    /// // Detach the node "1".
    /// node.detach();
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
    pub fn detach(&mut self) {
        self.forest.hierarchy.detach(self.id);
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
    /// let mut node = forest.node_mut(child_1)
    ///     .expect("the node must be alive");
    /// // Detach the single node "1".
    /// node.detach_single();
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
    pub fn detach_single(&mut self) -> Result<(), StructureError> {
        self.forest.hierarchy.detach_single(self.id)
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
    /// let mut node = forest.node_mut(child_1_1)
    ///     .expect("the node must be alive");
    /// node.remove_hooked_panic_safe(|data| {
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
    #[inline]
    pub fn remove_hooked_panic_safe<F: FnMut(T)>(self, f: F) {
        self.forest.remove_hooked_panic_safe(self.id, f)
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
    /// let mut node = forest.node_mut(child_1_1)
    ///     .expect("the node must be alive");
    /// node.remove_hooked(|data| {
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
    #[inline]
    pub fn remove_hooked<F: FnMut(T)>(self, f: F) {
        self.forest.remove_hooked(self.id, f)
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
    /// let mut node = forest.node_mut(child_1_1)
    ///     .expect("the node must be alive");
    /// node.remove();
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
    pub fn remove(self) {
        self.forest.remove(self.id);
    }
}

/// Debug printing.
impl<'a, T> NodeMut<'a, T> {
    /// Returns the pretty-printable proxy object to the node and descendants.
    ///
    /// This requires `debug-print` feature to be enabled.
    #[cfg(feature = "debug-print")]
    #[cfg_attr(feature = "docsrs", doc(cfg(feature = "debug-print")))]
    pub fn debug_print(&self) -> DebugPrint<'_, T> {
        DebugPrint::new(self.node())
    }
}

/// Returns an iterator with the first element skipped.
#[inline]
fn first_skipped<I: Iterator>(mut iter: I) -> I {
    iter.next();
    iter
}

/// Returns an iterator with the last element skipped.
#[inline]
fn last_skipped<I: DoubleEndedIterator>(mut iter: I) -> I {
    iter.next_back();
    iter
}

#[cfg(test)]
mod tests {
    use super::Forest;

    use alloc::vec::Vec;

    use crate::dynamic::forest::traverse::DftEvent;
    use crate::dynamic::{AdoptAs, InsertAs};

    mod insert {
        use super::*;

        #[test]
        fn unchanged_first_child_of_parent() {
            let mut forest = Forest::new();
            let root = forest.create_root("root");
            assert_eq!(
                forest
                    .node(root)
                    .expect("the node must be alive")
                    .depth_first_traverse()
                    .map(|ev| ev.map(|node| *node.data()))
                    .collect::<Vec<_>>(),
                &[DftEvent::Open("root"), DftEvent::Close("root"),]
            );

            let mut node = forest.node_mut(root).expect("the node must be alive");

            // Create a new node.
            // Create a node "new" and insert it as the first child of the node "root".
            let new = node.create("new", AdoptAs::FirstChild);
            assert_eq!(
                forest
                    .node(root)
                    .expect("the node must be alive")
                    .depth_first_traverse()
                    .map(|ev| ev.map(|node| *node.data()))
                    .collect::<Vec<_>>(),
                &[
                    DftEvent::Open("root"),
                    DftEvent::Open("new"),
                    DftEvent::Close("new"),
                    DftEvent::Close("root"),
                ]
            );

            // Re-insert the "new" node to the same position (i.e. do nothing).
            forest
                .insert(new, InsertAs::FirstChildOf(root))
                .expect("changing nothing should succeed");

            assert_eq!(
                forest
                    .node(root)
                    .expect("the node must be alive")
                    .depth_first_traverse()
                    .map(|ev| ev.map(|node| *node.data()))
                    .collect::<Vec<_>>(),
                &[
                    DftEvent::Open("root"),
                    DftEvent::Open("new"),
                    DftEvent::Close("new"),
                    DftEvent::Close("root"),
                ]
            );
        }
    }

    mod adopt {
        use super::*;

        #[test]
        fn unchanged_first_child_of_parent() {
            let mut forest = Forest::new();
            let root = forest.create_root("root");
            assert_eq!(
                forest
                    .node(root)
                    .expect("the node must be alive")
                    .depth_first_traverse()
                    .map(|ev| ev.map(|node| *node.data()))
                    .collect::<Vec<_>>(),
                &[DftEvent::Open("root"), DftEvent::Close("root"),]
            );

            let mut node = forest.node_mut(root).expect("the node must be alive");

            // Create a new node.
            // Create a node "new" and insert it as the first child of the node "root".
            let new = node.create("new", AdoptAs::FirstChild);
            assert_eq!(
                forest
                    .node(root)
                    .expect("the node must be alive")
                    .depth_first_traverse()
                    .map(|ev| ev.map(|node| *node.data()))
                    .collect::<Vec<_>>(),
                &[
                    DftEvent::Open("root"),
                    DftEvent::Open("new"),
                    DftEvent::Close("new"),
                    DftEvent::Close("root"),
                ]
            );

            let mut node = forest.node_mut(root).expect("the node must be alive");
            // Re-insert the "new" node to the same position (i.e. do nothing).
            node.adopt(new, AdoptAs::FirstChild);

            assert_eq!(
                forest
                    .node(root)
                    .expect("the node must be alive")
                    .depth_first_traverse()
                    .map(|ev| ev.map(|node| *node.data()))
                    .collect::<Vec<_>>(),
                &[
                    DftEvent::Open("root"),
                    DftEvent::Open("new"),
                    DftEvent::Close("new"),
                    DftEvent::Close("root"),
                ]
            );
        }
    }
}
