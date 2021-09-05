//! Tree traversal.

use crate::dynamic::hierarchy::Hierarchy;
use crate::dynamic::NodeId;

/// Depth-first traverseal event.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DftEvent {
    /// Node open.
    Open(NodeId),
    /// Node close.
    Close(NodeId),
}

/// Double-ended depth-first tree traverser.
#[derive(Debug, Clone, Copy)]
pub(crate) struct DepthFirstTraverser {
    /// Next event to emit forward and backward.
    next: Option<(DftEvent, DftEvent)>,
}

impl DepthFirstTraverser {
    /// Creates a traverser from a toplevel node.
    ///
    /// The toplevel does not need to be the root of a tree.
    #[must_use]
    pub(crate) fn with_toplevel(id: NodeId) -> Self {
        Self {
            next: Some((DftEvent::Open(id), DftEvent::Close(id))),
        }
    }

    /// Traverses the tree forward and returns the next node event.
    pub(crate) fn next(&mut self, hier: &Hierarchy) -> Option<DftEvent> {
        let (next, next_back) = self.next?;
        match self.next_of_next_forward(hier) {
            Some(next_of_next) => {
                self.next = Some((next_of_next, next_back));
            }
            None => {
                self.next = None;
            }
        }
        Some(next)
    }

    /// Traverses the tree backward and returns the next node event.
    pub(crate) fn next_back(&mut self, hier: &Hierarchy) -> Option<DftEvent> {
        let (next, next_back) = self.next?;
        match self.next_of_next_backward(hier) {
            Some(next_of_next_back) => {
                self.next = Some((next, next_of_next_back));
            }
            None => {
                self.next = None;
            }
        }
        Some(next_back)
    }

    /// Traverses the tree forward and returns the next event of the next event.
    fn next_of_next_forward(&mut self, hier: &Hierarchy) -> Option<DftEvent> {
        let (next, next_back) = self.next?;
        if next == next_back {
            // The next event is the last event.
            return None;
        }
        match next {
            DftEvent::Open(id) => {
                // Dive into the first child if available, or leave the node.
                let neighbors = hier
                    .neighbors(id)
                    .expect("[consistency] the node being traversed must be alive");
                Some(match neighbors.first_child() {
                    Some(first_child) => DftEvent::Open(first_child),
                    None => DftEvent::Close(id),
                })
            }
            DftEvent::Close(id) => {
                // Dive into the next sibling if available, or leave the parent.
                let neighbors = hier
                    .neighbors(id)
                    .expect("[consistency] the node being traversed must be alive");
                Some(match neighbors.next_sibling() {
                    Some(next_sibling) => DftEvent::Open(next_sibling),
                    None => {
                        // If the next event is `Close(root)`, the code must have
                        // returned earlily and does not come here.
                        let parent = neighbors.parent().expect(
                            "[consistency] parent node must exist since the node is not the root",
                        );
                        DftEvent::Close(parent)
                    }
                })
            }
        }
    }

    /// Traverses the tree backward and returns the next event of the next event.
    fn next_of_next_backward(&mut self, hier: &Hierarchy) -> Option<DftEvent> {
        let (next, next_back) = self.next?;
        if next == next_back {
            // The next event is the last event.
            return None;
        }
        match next {
            DftEvent::Close(id) => {
                // Dive into the last child if available, or leave the node.
                let neighbors = hier
                    .neighbors(id)
                    .expect("[consistency] the node being traversed must be alive");
                Some(match neighbors.last_child(hier) {
                    Some(last_child) => DftEvent::Close(last_child),
                    None => DftEvent::Open(id),
                })
            }
            DftEvent::Open(id) => {
                // Dive into the previous sibling if available, or leave the parent.
                let neighbors = hier
                    .neighbors(id)
                    .expect("[consistency] the node being traversed must be alive");
                Some(match neighbors.prev_sibling(hier) {
                    Some(prev_sibling) => DftEvent::Close(prev_sibling),
                    None => {
                        // If the next event is `Open(root)`, the code must have
                        // returned earlily and does not come here.
                        let parent = neighbors.parent().expect(
                            "[consistency] parent node must exist since the node is not the root",
                        );
                        DftEvent::Open(parent)
                    }
                })
            }
        }
    }
}

/// Ancestors traverser.
///
/// Note that this returns the starting node first.
#[derive(Debug, Clone, Copy)]
pub struct AncestorsTraverser {
    /// Next event to emit.
    next: Option<NodeId>,
}

impl AncestorsTraverser {
    /// Creates a traverser from the node.
    #[inline]
    #[must_use]
    pub(crate) fn with_start(id: NodeId) -> Self {
        // Return the starting node first.
        Self { next: Some(id) }
    }

    /// Creates a traverser from the node.
    #[must_use]
    pub(crate) fn next(&mut self, hier: &Hierarchy) -> Option<NodeId> {
        let next = self.next?;
        self.next = hier
            .neighbors(next)
            .expect("[consistency] the node being traversed must be alive")
            .parent();

        Some(next)
    }
}

/// Double-ended siblings traverser.
#[derive(Debug, Clone, Copy)]
pub struct SiblingsTraverser {
    /// Next event to emit forward and backward.
    next: Option<(NodeId, NodeId)>,
}

impl SiblingsTraverser {
    /// Creates a traverser from the parent.
    #[inline]
    #[must_use]
    pub(crate) fn with_parent(parent: NodeId, hier: &Hierarchy) -> Self {
        let neighbors = hier
            .neighbors(parent)
            .expect("[consistency] the node being traversed must be alive");
        let next = neighbors.first_last_child(hier);

        Self { next }
    }

    /// Creates a traverser from the first sibling in the range.
    #[inline]
    #[must_use]
    pub(crate) fn with_first_sibling(first: NodeId, hier: &Hierarchy) -> Self {
        let parent = hier
            .neighbors(first)
            .expect("[consistency] the node being traversed must be alive")
            .parent();
        let last = parent
            .and_then(|parent| hier.neighbors(parent))
            .map_or(first, |neighbors| {
                neighbors
                    .last_child(hier)
                    .expect("[consistency] the parent must have children `first`")
            });

        Self {
            next: Some((first, last)),
        }
    }

    /// Creates a traverser from the last sibling in the range.
    #[inline]
    #[must_use]
    pub(crate) fn with_last_sibling(last: NodeId, hier: &Hierarchy) -> Self {
        let parent = hier
            .neighbors(last)
            .expect("[consistency] the node being traversed must be alive")
            .parent();
        let first = parent
            .and_then(|parent| hier.neighbors(parent))
            .map_or(last, |neighbors| {
                neighbors
                    .first_child()
                    .expect("[consistency] the parent must have children `last`")
            });

        Self {
            next: Some((first, last)),
        }
    }

    /// Traverses the tree forward and returns the next node event.
    pub(crate) fn next(&mut self, hier: &Hierarchy) -> Option<NodeId> {
        let (next, next_back) = self.next?;
        match self.next_of_next_forward(hier) {
            Some(next_of_next) => {
                self.next = Some((next_of_next, next_back));
            }
            None => {
                self.next = None;
            }
        }
        Some(next)
    }

    /// Traverses the tree backward and returns the next node event.
    pub(crate) fn next_back(&mut self, hier: &Hierarchy) -> Option<NodeId> {
        let (next, next_back) = self.next?;
        match self.next_of_next_backward(hier) {
            Some(next_of_next_back) => {
                self.next = Some((next, next_of_next_back));
            }
            None => {
                self.next = None;
            }
        }
        Some(next_back)
    }

    /// Traverses the tree forward and returns the next event of the next event.
    fn next_of_next_forward(&mut self, hier: &Hierarchy) -> Option<NodeId> {
        let (next, next_back) = self.next?;
        if next == next_back {
            // The next event is the last event.
            return None;
        }
        let neighbors = hier
            .neighbors(next)
            .expect("[consistency] the node being traversed must be alive");
        neighbors.next_sibling()
    }

    /// Traverses the tree backward and returns the next event of the next event.
    fn next_of_next_backward(&mut self, hier: &Hierarchy) -> Option<NodeId> {
        let (next, next_back) = self.next?;
        if next == next_back {
            // The next event is the last event.
            return None;
        }
        let neighbors = hier
            .neighbors(next_back)
            .expect("[consistency] the node being traversed must be alive");
        neighbors.prev_sibling(hier)
    }
}
