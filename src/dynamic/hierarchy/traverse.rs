//! Tree traversal.

use alloc::collections::VecDeque;

use crate::dynamic::hierarchy::Hierarchy;
use crate::dynamic::InternalNodeId;
use crate::nonmax::NonMaxUsize;

/// Depth-first traversal event.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DftEvent<Id> {
    /// Node open.
    Open(Id),
    /// Node close.
    Close(Id),
}

/// Double-ended depth-first tree traverser.
#[derive(Debug, Clone, Copy)]
pub(crate) struct DepthFirstTraverser<Id> {
    /// Next event to emit forward and backward.
    next: Option<(DftEvent<Id>, DftEvent<Id>)>,
}

impl<Id: InternalNodeId> DepthFirstTraverser<Id> {
    /// Creates a traverser from a toplevel node.
    ///
    /// The toplevel does not need to be the root of a tree.
    ///
    /// # Panics
    ///
    /// Panics if the given node is not alive.
    #[must_use]
    pub(crate) fn with_toplevel(id: Id, hier: &Hierarchy<Id>) -> Self {
        if !hier.is_alive(id) {
            panic!("[precondition] the node to be traversed must be alive");
        }

        Self {
            next: Some((DftEvent::Open(id), DftEvent::Close(id))),
        }
    }

    /// Traverses the tree forward and returns the next node event.
    pub(crate) fn next(&mut self, hier: &Hierarchy<Id>) -> Option<DftEvent<Id>> {
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
    pub(crate) fn next_back(&mut self, hier: &Hierarchy<Id>) -> Option<DftEvent<Id>> {
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
    fn next_of_next_forward(&mut self, hier: &Hierarchy<Id>) -> Option<DftEvent<Id>> {
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
    fn next_of_next_backward(&mut self, hier: &Hierarchy<Id>) -> Option<DftEvent<Id>> {
        let (next, next_back) = self.next?;
        if next == next_back {
            // The next event is the last event.
            return None;
        }
        match next_back {
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

    /// Returns the next event without advancing the iterator.
    #[must_use]
    pub(crate) fn peek(&self) -> Option<DftEvent<Id>> {
        self.next.map(|(forward, _back)| forward)
    }

    /// Returns the backward next event without advancing the iterator.
    #[must_use]
    pub(crate) fn peek_back(&self) -> Option<DftEvent<Id>> {
        self.next.map(|(_fwd, back)| back)
    }
}

/// Ancestors traverser.
///
/// Note that this returns the starting node first.
#[derive(Debug, Clone, Copy)]
pub struct AncestorsTraverser<Id> {
    /// Next event to emit.
    next: Option<Id>,
}

impl<Id: InternalNodeId> AncestorsTraverser<Id> {
    /// Creates a traverser from the node.
    ///
    /// # Panics
    ///
    /// Panics if the given node is not alive.
    #[inline]
    #[must_use]
    pub(crate) fn with_start(id: Id, hier: &Hierarchy<Id>) -> Self {
        if !hier.is_alive(id) {
            panic!("[precondition] the node to be traversed must be alive");
        }

        // Return the starting node first.
        Self { next: Some(id) }
    }

    /// Creates a traverser from the node.
    #[must_use]
    pub(crate) fn next(&mut self, hier: &Hierarchy<Id>) -> Option<Id> {
        let next = self.next?;
        self.next = hier
            .neighbors(next)
            .expect("[consistency] the node being traversed must be alive")
            .parent();

        Some(next)
    }

    /// Returns the next event without advancing the iterator.
    #[inline]
    #[must_use]
    pub(crate) fn peek(&self) -> Option<Id> {
        self.next
    }
}

/// Double-ended siblings traverser.
#[derive(Debug, Clone, Copy)]
pub struct SiblingsTraverser<Id> {
    /// Next event to emit forward and backward.
    next: Option<(Id, Id)>,
}

impl<Id: InternalNodeId> SiblingsTraverser<Id> {
    /// Creates a traverser from the parent.
    ///
    /// # Panics
    ///
    /// Panics if the given node is not alive.
    #[inline]
    #[must_use]
    pub(crate) fn with_parent(parent: Id, hier: &Hierarchy<Id>) -> Self {
        let neighbors = hier
            .neighbors(parent)
            .expect("[precondition] the node being traversed must be alive");
        let next = neighbors.first_last_child(hier);

        Self { next }
    }

    /// Creates a traverser from the first sibling in the range.
    ///
    /// # Panics
    ///
    /// Panics if the given node is not alive.
    #[inline]
    #[must_use]
    pub(crate) fn with_first_sibling(first: Id, hier: &Hierarchy<Id>) -> Self {
        let parent = hier
            .neighbors(first)
            .expect("[precondition] the node being traversed must be alive")
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
    ///
    /// # Panics
    ///
    /// Panics if the given node is not alive.
    #[inline]
    #[must_use]
    pub(crate) fn with_last_sibling(last: Id, hier: &Hierarchy<Id>) -> Self {
        let parent = hier
            .neighbors(last)
            .expect("[precondition] the node being traversed must be alive")
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
    pub(crate) fn next(&mut self, hier: &Hierarchy<Id>) -> Option<Id> {
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
    pub(crate) fn next_back(&mut self, hier: &Hierarchy<Id>) -> Option<Id> {
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
    fn next_of_next_forward(&mut self, hier: &Hierarchy<Id>) -> Option<Id> {
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
    fn next_of_next_backward(&mut self, hier: &Hierarchy<Id>) -> Option<Id> {
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

    /// Returns the next event without advancing the iterator.
    #[must_use]
    pub(crate) fn peek(&self) -> Option<Id> {
        self.next.map(|(forward, _back)| forward)
    }

    /// Returns the backward next event without advancing the iterator.
    #[must_use]
    pub(crate) fn peek_back(&self) -> Option<Id> {
        self.next.map(|(_fwd, back)| back)
    }
}

/// Limited depth-first tree traverser in "safe mode".
///
/// # Guarantees
///
/// This traverser allows the tree to be modified in some way during the
/// traversal.
///
/// Nodes already visited and have been left (i.e. `DftEvent::Close(node)` has
/// been emitted) can be modified freely. The traverser is guaranteed not to
/// refer such nodes after leaving them.
#[derive(Debug, Clone, Copy)]
pub(crate) struct SafeModeDepthFirstTraverser<Id> {
    /// Next event to emit.
    next: Option<DftEvent<Id>>,
    /// Root node of the traversal.
    root: Id,
}

impl<Id: InternalNodeId> SafeModeDepthFirstTraverser<Id> {
    /// Creates a traverser from a toplevel node.
    ///
    /// The toplevel does not need to be the root of a tree.
    ///
    /// # Panics
    ///
    /// Panics if the given node is not alive.
    #[must_use]
    pub(crate) fn new(root: Id, hier: &Hierarchy<Id>) -> Self {
        if !hier.is_alive(root) {
            panic!("[precondition] the node to be traversed must be alive");
        }

        Self {
            next: Some(DftEvent::Open(root)),
            root,
        }
    }

    /// Traverses the tree forward and returns the next node event.
    pub(crate) fn next(&mut self, hier: &Hierarchy<Id>) -> Option<DftEvent<Id>> {
        let next = self.next?;
        self.next = self.next_of_next(hier);
        Some(next)
    }

    /// Traverses the tree knd returns the next event of the next event.
    fn next_of_next(&mut self, hier: &Hierarchy<Id>) -> Option<DftEvent<Id>> {
        let next = self.next?;
        if next == DftEvent::Close(self.root) {
            // The next event is the last event.
            return None;
        }
        let next_of_next = match next {
            DftEvent::Open(id) => {
                // Dive into the first child if available, or leave the node.
                let neighbors = hier
                    .neighbors(id)
                    .expect("[consistency] the current node must be alive");
                match neighbors.first_child() {
                    Some(first_child) => DftEvent::Open(first_child),
                    None => DftEvent::Close(id),
                }
            }
            DftEvent::Close(id) => {
                // Dive into the next sibling if available, or leave the parent.
                let neighbors = hier
                    .neighbors(id)
                    .expect("[consistency] the current node must be alive");
                match neighbors.next_sibling() {
                    Some(next_sibling) => DftEvent::Open(next_sibling),
                    None => {
                        // If the next event is `Close(root)`, the code must have
                        // returned earlily and does not come here.
                        debug_assert_ne!(
                            id, self.root,
                            "[consistency] closing of the root must have been handled specially"
                        );
                        let parent = neighbors.parent().expect(
                            "[consistency] parent node must exist since the node is not the root",
                        );
                        DftEvent::Close(parent)
                    }
                }
            }
        };

        Some(next_of_next)
    }
}

/// Double-ended limited-depth depth-first tree traverser.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ShallowDepthFirstTraverser<Id> {
    /// Next event and the node depth to emit forward and backward.
    #[allow(clippy::type_complexity)]
    next: Option<((DftEvent<Id>, usize), (DftEvent<Id>, usize))>,
    /// Maximum depth.
    max_depth: Option<NonMaxUsize>,
}

impl<Id: InternalNodeId> ShallowDepthFirstTraverser<Id> {
    /// Creates a traverser from a toplevel node.
    ///
    /// The toplevel does not need to be the root of a tree.
    ///
    /// # Panics
    ///
    /// Panics if the given node is not alive.
    #[must_use]
    pub(crate) fn with_toplevel_and_max_depth(
        id: Id,
        hier: &Hierarchy<Id>,
        max_depth: Option<usize>,
    ) -> Self {
        if !hier.is_alive(id) {
            panic!("[precondition] the node to be traversed must be alive");
        }

        // The number of the nodes cannot reach `usize::MAX` since the node ID
        // is internally `NonMaxUsize`. This means that `Some(usize::MAX)` is
        // in fact identical to "no depth limit", so it can be collapsed
        // to `None`.
        let max_depth = max_depth.and_then(NonMaxUsize::new);

        Self {
            next: Some(((DftEvent::Open(id), 0), (DftEvent::Close(id), 0))),
            max_depth,
        }
    }

    /// Returns the allowed max depth.
    #[inline]
    #[must_use]
    pub(crate) fn max_depth(&self) -> Option<usize> {
        self.max_depth.map(|v| v.get())
    }

    /// Traverses the tree forward and returns the next node event and depth.
    pub(crate) fn next(&mut self, hier: &Hierarchy<Id>) -> Option<(DftEvent<Id>, usize)> {
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

    /// Traverses the tree backward and returns the next node event and depth.
    pub(crate) fn next_back(&mut self, hier: &Hierarchy<Id>) -> Option<(DftEvent<Id>, usize)> {
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
    fn next_of_next_forward(&mut self, hier: &Hierarchy<Id>) -> Option<(DftEvent<Id>, usize)> {
        let (next, next_back) = self.next?;
        if next == next_back {
            // The next event is the last event.
            return None;
        }

        let (next, next_depth) = next;
        match next {
            DftEvent::Open(id) => {
                // Leave the node if the current node is at maximum depth.
                if Some(next_depth) == self.max_depth() {
                    return Some((DftEvent::Close(id), next_depth));
                }
                // Dive into the first child if available, or leave the node.
                let neighbors = hier
                    .neighbors(id)
                    .expect("[consistency] the node being traversed must be alive");
                Some(match neighbors.first_child() {
                    Some(first_child) => (DftEvent::Open(first_child), next_depth + 1),
                    None => (DftEvent::Close(id), next_depth),
                })
            }
            DftEvent::Close(id) => {
                // Dive into the next sibling if available, or leave the parent.
                let neighbors = hier
                    .neighbors(id)
                    .expect("[consistency] the node being traversed must be alive");
                Some(match neighbors.next_sibling() {
                    Some(next_sibling) => (DftEvent::Open(next_sibling), next_depth),
                    None => {
                        // If the next event is `Close(root)`, the code must have
                        // returned earlily and does not come here.
                        let parent = neighbors.parent().expect(
                            "[consistency] parent node must exist since the node is not the root",
                        );
                        (DftEvent::Close(parent), next_depth - 1)
                    }
                })
            }
        }
    }

    /// Traverses the tree backward and returns the next event of the next event.
    fn next_of_next_backward(&mut self, hier: &Hierarchy<Id>) -> Option<(DftEvent<Id>, usize)> {
        let (next, next_back) = self.next?;
        if next == next_back {
            // The next event is the last event.
            return None;
        }

        let (next_back, next_depth) = next_back;
        match next_back {
            DftEvent::Close(id) => {
                // Leave the node if the current node is at maximum depth.
                if Some(next_depth) == self.max_depth() {
                    return Some((DftEvent::Open(id), next_depth));
                }
                // Dive into the last child if available, or leave the node.
                let neighbors = hier
                    .neighbors(id)
                    .expect("[consistency] the node being traversed must be alive");
                Some(match neighbors.last_child(hier) {
                    Some(last_child) => (DftEvent::Close(last_child), next_depth + 1),
                    None => (DftEvent::Open(id), next_depth),
                })
            }
            DftEvent::Open(id) => {
                // Dive into the previous sibling if available, or leave the parent.
                let neighbors = hier
                    .neighbors(id)
                    .expect("[consistency] the node being traversed must be alive");
                Some(match neighbors.prev_sibling(hier) {
                    Some(prev_sibling) => (DftEvent::Close(prev_sibling), next_depth),
                    None => {
                        // If the next event is `Open(root)`, the code must have
                        // returned earlily and does not come here.
                        let parent = neighbors.parent().expect(
                            "[consistency] parent node must exist since the node is not the root",
                        );
                        (DftEvent::Open(parent), next_depth - 1)
                    }
                })
            }
        }
    }

    /// Returns the next event without advancing the iterator.
    #[must_use]
    pub(crate) fn peek(&self) -> Option<(DftEvent<Id>, usize)> {
        self.next.map(|(forward, _back)| forward)
    }

    /// Returns the backward next event without advancing the iterator.
    #[must_use]
    pub(crate) fn peek_back(&self) -> Option<(DftEvent<Id>, usize)> {
        self.next.map(|(_fwd, back)| back)
    }
}

/// Breadth-first tree traverser.
///
/// This traverser does not heap-allocate.
///
/// Note that traversing all nodes will be `O(n^2)` operation in worst case,
/// not `O(n)`.
#[derive(Debug, Clone, Copy)]
pub(crate) struct BreadthFirstTraverser<Id> {
    /// Internal shallow depth-first traverser.
    inner: ShallowDepthFirstTraverser<Id>,
    /// Root node.
    ///
    /// If this is `None`, it means that the iteration has been completed.
    root: Option<Id>,
    /// Currently iterating depth.
    current_depth: usize,
}

impl<Id: InternalNodeId> BreadthFirstTraverser<Id> {
    /// Creates a traverser from a toplevel node.
    ///
    /// The toplevel does not need to be the root of a tree.
    ///
    /// # Panics
    ///
    /// Panics if the given node is not alive.
    #[must_use]
    pub(crate) fn with_toplevel(id: Id, hier: &Hierarchy<Id>) -> Self {
        if !hier.is_alive(id) {
            panic!("[precondition] the node to be traversed must be alive");
        }

        Self {
            inner: ShallowDepthFirstTraverser::with_toplevel_and_max_depth(id, hier, Some(0)),
            root: Some(id),
            current_depth: 0,
        }
    }

    /// Traverses the tree and returns the next node ID.
    pub(crate) fn next(&mut self, hier: &Hierarchy<Id>) -> Option<(Id, usize)> {
        let root = self.root?;

        if let Some(id) = self.next_inner(hier) {
            return Some((id, self.current_depth));
        }

        // Go to the next level.
        self.current_depth += 1;
        self.inner = ShallowDepthFirstTraverser::with_toplevel_and_max_depth(
            root,
            hier,
            Some(self.current_depth),
        );

        // Retry for the next level.
        if let Some(id) = self.next_inner(hier) {
            return Some((id, self.current_depth));
        }
        // If failed, no more nodes with the current depth.
        // All nodes are iterated.
        self.root = None;
        None
    }

    /// Returns the next node open event with the current depth.
    fn next_inner(&mut self, hier: &Hierarchy<Id>) -> Option<Id> {
        while let Some((ev, depth)) = self.inner.next(hier) {
            if depth == self.current_depth {
                if let DftEvent::Open(id) = ev {
                    return Some(id);
                }
            }
        }

        None
    }
}

/// Queued event for breadth-first traversal.
///
/// The size of this type must be equal to the size of `NodeId` itself, due to
/// niche optimization.
#[derive(Debug, Clone, Copy)]
enum BftQueuedEvent<Id> {
    /// Node at the current level.
    Node(Id),
    /// No more nodes at the current level. Increment the depth.
    IncrementDepth,
}

/// Allocating breadth-first tree traverser.
///
/// This traverser heap-allocates, and iterating all nodes is `O(n)` operation.
#[derive(Debug, Clone)]
pub(crate) struct AllocatingBreadthFirstTraverser<Id> {
    /// Queued events.
    // This queue must have zero or one `BftQueuedEvent::IncrementDepth` at any
    // moment.
    events: VecDeque<BftQueuedEvent<Id>>,
    /// Currently iterating depth.
    current_depth: usize,
}

impl<Id: InternalNodeId> AllocatingBreadthFirstTraverser<Id> {
    /// Creates a traverser from a toplevel node.
    ///
    /// The toplevel does not need to be the root of a tree.
    ///
    /// # Panics
    ///
    /// Panics if the given node is not alive.
    #[must_use]
    pub(crate) fn with_toplevel(id: Id, hier: &Hierarchy<Id>) -> Self {
        if !hier.is_alive(id) {
            panic!("[precondition] the node to be traversed must be alive");
        }

        let mut events = VecDeque::new();
        events.push_back(BftQueuedEvent::Node(id));
        events.push_back(BftQueuedEvent::IncrementDepth);
        Self {
            events,
            current_depth: 0,
        }
    }

    /// Traverses the tree and returns the next node ID and depth.
    pub(crate) fn next(&mut self, hier: &Hierarchy<Id>) -> Option<(Id, usize)> {
        while let Some(ev) = self.events.pop_front() {
            let next = match ev {
                BftQueuedEvent::Node(v) => v,
                BftQueuedEvent::IncrementDepth => {
                    if self.events.is_empty() {
                        // No more events to emit.
                        // Release the buffer since it won't be used anymore.
                        self.events = Default::default();
                        return None;
                    }
                    self.current_depth += 1;
                    self.events.push_back(BftQueuedEvent::IncrementDepth);
                    continue;
                }
            };

            // Get children of the node and push them to the next-depth queue.
            {
                let mut next_child = hier
                    .neighbors(next)
                    .expect("[consistency] the node to be traversed must be alive")
                    .first_child();
                while let Some(child) = next_child {
                    self.events.push_back(BftQueuedEvent::Node(child));
                    next_child = hier
                        .neighbors(child)
                        .expect("[consistency] the node to be traversed must be alive")
                        .next_sibling();
                }
            }

            return Some((next, self.current_depth));
        }

        None
    }

    /// Returns the size hint in iterator-like manner.
    pub(crate) fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.events.len();
        // Note that `len == 1` implies that the queue has only
        // `BftQueuedEvent::IncrementDepth`.
        if len <= 1 {
            (0, Some(0))
        } else {
            (len - 1, None)
        }
    }

    /// Returns the next event without advancing the iterator.
    #[inline]
    #[must_use]
    pub(crate) fn peek(&self) -> Option<(Id, usize)> {
        match *self.events.front()? {
            BftQueuedEvent::Node(next) => Some((next, self.current_depth)),
            BftQueuedEvent::IncrementDepth => match *self.events.get(1)? {
                BftQueuedEvent::Node(next) => Some((next, self.current_depth + 1)),
                BftQueuedEvent::IncrementDepth => panic!(
                    "[consistency] `IncrementDepth` must not appear right after `IncrementDepth`"
                ),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use core::mem;

    use crate::dynamic::NodeIdUsize;

    #[test]
    fn bft_queued_event_niche_optimized() {
        assert_eq!(
            mem::size_of::<BftQueuedEvent<NodeIdUsize>>(),
            mem::size_of::<NodeIdUsize>(),
            "`BftQueuedEvent` type must have the same size as \
             `NodeId` type due to niche optimization"
        );
    }
}
