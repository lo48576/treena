//! Node.

use crate::dynamic::{Forest, NodeId};

/// Immutable reference to a node.
///
/// This type guarantees that the node ID must be present in the internal
/// storage of the tree and must not be removed yet.
#[derive(Debug, Clone, Copy)]
pub struct Node<'a, T> {
    /// Forest.
    forest: &'a Forest<T>,
    /// Node ID.
    id: NodeId,
}

impl<'a, T> Node<'a, T> {
    /// Creates a new `Node` object.
    #[must_use]
    pub(super) fn new(forest: &'a Forest<T>, id: NodeId) -> Option<Self> {
        if !forest.is_alive(id) {
            return None;
        }
        Some(Self { forest, id })
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
