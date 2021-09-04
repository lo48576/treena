//! Dynamic hierarchy for trees and forests.

use core::fmt;

use alloc::vec::Vec;

use crate::dynamic::NodeId;

/// A forest without custom data tied to nodes.
#[derive(Default, Debug, Clone)]
pub(crate) struct Hierarchy {
    /// Neighbors storage.
    neighbors: Vec<Neighbors>,
}

impl Hierarchy {
    /// Creates a new root node.
    ///
    /// # Panics
    ///
    /// Panics if the node ID overflows.
    pub(crate) fn create_root(&mut self) -> NodeId {
        let new_id = NodeId::from_usize(self.neighbors.len())
            .expect("[precondition] node ID overflowed presumably due to too many node creations");
        self.neighbors.push(Neighbors::new_root(new_id));

        new_id
    }

    /// Returns a reference to the neighbors for the node.
    #[inline]
    #[must_use]
    #[allow(dead_code)] // TODO: Remove this.
    pub(crate) fn neighbors(&self, id: NodeId) -> Option<&Neighbors> {
        self.neighbors.get(id.get())
    }
}

/// Neighbors.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct Neighbors {
    /// Parent.
    parent: Option<NodeId>,
    /// Cyclic previous sibling.
    ///
    /// `None` if the node has already been removed.
    /// If the node is alive and is the first sibling, node ID of the last sibling.
    /// Otherwise (i.e. the node is alive but is not the first sibling),
    /// node ID of the previous sibling.
    ///
    /// By making this field cyclic, "last child" field becomes unnecessary.
    ///
    /// See
    /// <http://www.aosabook.org/en/posa/parsing-xml-at-the-speed-of-light.html#data-structures-for-the-document-object-model>.
    prev_sibling_cyclic: Option<NodeId>,
    /// Next sibling.
    next_sibling: Option<NodeId>,
    /// First child.
    first_child: Option<NodeId>,
}

impl Neighbors {
    /// Creates a new `Neighbors` that is not connected to anyone.
    #[inline]
    #[must_use]
    fn new_root(id: NodeId) -> Self {
        Self {
            parent: None,
            prev_sibling_cyclic: Some(id),
            next_sibling: None,
            first_child: None,
        }
    }
}

// For compact printing.
impl fmt::Debug for Neighbors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        /// A wrapper to print optional node ID in compact form.
        #[derive(Clone, Copy)]
        struct OptNodeId(Option<NodeId>);
        impl fmt::Debug for OptNodeId {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self.0 {
                    Some(id) => id.fmt(f),
                    None => f.write_str("None"),
                }
            }
        }

        f.debug_struct("Neighbors")
            .field("parent", &OptNodeId(self.parent))
            .field("prev_sibling_cyclic", &OptNodeId(self.prev_sibling_cyclic))
            .field("next_sibling", &OptNodeId(self.next_sibling))
            .field("first_child", &OptNodeId(self.first_child))
            .finish()
    }
}
