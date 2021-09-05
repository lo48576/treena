//! Dynamic hierarchy for trees and forests.

pub(crate) mod traverse;

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

    /// Returns a reference to the neighbors for the node if the node is alive.
    ///
    /// Returns `None` if the node ID is invalid or the node has already been removed.
    #[must_use]
    pub(crate) fn neighbors(&self, id: NodeId) -> Option<&Neighbors> {
        self.neighbors.get(id.get()).filter(|v| v.is_alive())
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

    /// Returns true if the node is alive.
    #[inline]
    #[must_use]
    fn is_alive(&self) -> bool {
        self.prev_sibling_cyclic.is_some()
    }

    /// Returns the node ID of the parent.
    ///
    /// # Panics
    ///
    /// Panics if the `self` node has already been removed.
    #[inline]
    #[must_use]
    pub(crate) fn parent(&self) -> Option<NodeId> {
        if !self.is_alive() {
            panic!("[precondition] the node must be alive");
        }
        self.parent
    }

    /// Returns the node ID of the next sibling.
    ///
    /// # Panics
    ///
    /// Panics if the `self` node has already been removed.
    #[inline]
    #[must_use]
    pub(crate) fn next_sibling(&self) -> Option<NodeId> {
        if !self.is_alive() {
            panic!("[precondition] the node must be alive");
        }
        self.next_sibling
    }

    /// Returns the node ID of the previous sibling.
    ///
    /// # Panics
    ///
    /// Panics if the `self` node has already been removed.
    #[must_use]
    pub(crate) fn prev_sibling(&self, hier: &Hierarchy) -> Option<NodeId> {
        let prev_sibling_cyclic = match self.prev_sibling_cyclic {
            Some(v) => v,
            None => panic!("[precondition] the node must be alive"),
        };
        let prev_cyc_node = hier
            .neighbors(prev_sibling_cyclic)
            .expect("[consistency] the `prev_sibling_cyclic` node must be alive");

        // If `next_sibling` is available, `prev_sibling_cyclic` is a previous node.
        // If `next_sibling` is `None`, `prev_sibling_cyclic` is not a previous
        // node but the last sibling.
        prev_cyc_node.next_sibling.and(Some(prev_sibling_cyclic))
    }

    /// Returns the node ID of the first child.
    ///
    /// # Panics
    ///
    /// Panics if the `self` node has already been removed.
    #[inline]
    #[must_use]
    pub(crate) fn first_child(&self) -> Option<NodeId> {
        if !self.is_alive() {
            panic!("[precondition] the node must be alive");
        }
        self.first_child
    }

    /// Returns the node ID of the last child.
    ///
    /// # Panics
    ///
    /// Panics if the `self` node has already been removed.
    #[must_use]
    pub(crate) fn last_child(&self, hier: &Hierarchy) -> Option<NodeId> {
        self.first_last_child(hier).map(|(_first, last)| last)
    }

    /// Returns the node IDs of the first child and the last child.
    ///
    /// # Panics
    ///
    /// Panics if the `self` node has already been removed.
    #[inline]
    #[must_use]
    pub(crate) fn first_last_child(&self, hier: &Hierarchy) -> Option<(NodeId, NodeId)> {
        if !self.is_alive() {
            panic!("[precondition] the node must be alive");
        }

        let first_child = self.first_child()?;
        let last_child = hier
            .neighbors(first_child)
            .expect("[consistency] children of a live node must also be alive")
            .prev_sibling_cyclic;

        match last_child {
            Some(last_child) => Some((first_child, last_child)),
            None => panic!("[consistency] the last child must be alive"),
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
