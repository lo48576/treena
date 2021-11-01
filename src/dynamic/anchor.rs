//! Anchors.

use crate::dynamic::NodeIdUsize;

/// Relation of the node being `adopt`ed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AdoptAs {
    /// As the first child.
    FirstChild,
    /// As the last child.
    LastChild,
    /// As the previous sibling.
    PreviousSibling,
    /// As the next sibling.
    NextSibling,
}

impl AdoptAs {
    /// Creates `InsertAs` with the given anchor.
    #[must_use]
    pub(super) fn insert_with_anchor(self, anchor: NodeIdUsize) -> InsertAs {
        match self {
            Self::FirstChild => InsertAs::FirstChildOf(anchor),
            Self::LastChild => InsertAs::LastChildOf(anchor),
            Self::PreviousSibling => InsertAs::PreviousSiblingOf(anchor),
            Self::NextSibling => InsertAs::NextSiblingOf(anchor),
        }
    }
}

/// Target destination to insert, append, or prepend a node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
// All variants have the common suffix "Of", but this is intended.
// Variants would be used as, for example, `InsertAs::FirsChildOf(some_node)`.
#[allow(clippy::enum_variant_names)]
pub enum InsertAs {
    /// As the first child.
    FirstChildOf(NodeIdUsize),
    /// As the last child.
    LastChildOf(NodeIdUsize),
    /// As the previous sibling.
    PreviousSiblingOf(NodeIdUsize),
    /// As the next sibling.
    NextSiblingOf(NodeIdUsize),
}
