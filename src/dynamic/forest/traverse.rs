//! Tree traversal.

use core::iter;

use crate::dynamic::forest::{Forest, Node};
use crate::dynamic::hierarchy::traverse::{
    AllocatingBreadthFirstTraverser, AncestorsTraverser, BreadthFirstTraverser,
    DepthFirstTraverser, DftEvent as DftEventSrc, ShallowDepthFirstTraverser, SiblingsTraverser,
};
use crate::dynamic::NodeId;

/// Depth-first traverseal event.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DftEvent<T> {
    /// Node open.
    Open(T),
    /// Node close.
    Close(T),
}

impl<T> DftEvent<T> {
    /// Converts the internal value.
    pub fn map<F, U>(self, f: F) -> DftEvent<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Self::Open(v) => DftEvent::Open(f(v)),
            Self::Close(v) => DftEvent::Close(f(v)),
        }
    }

    /// Creates `DftEvent` from `hierarchy::traverse::DftEvent`.
    #[must_use]
    fn from_hierarchy_dft_event<U, F>(ev: DftEventSrc<U>, f: F) -> Self
    where
        F: FnOnce(U) -> T,
    {
        match ev {
            DftEventSrc::Open(v) => Self::Open(f(v)),
            DftEventSrc::Close(v) => Self::Close(f(v)),
        }
    }
}

/// Double-ended iterator for depth-first traversal.
#[derive(Debug, Clone)]
pub struct DepthFirstTraverse<'a, Id: NodeId, T> {
    /// Forest.
    forest: &'a Forest<Id, T>,
    /// Traverser.
    traverser: DepthFirstTraverser<Id::Internal>,
}

impl<'a, Id: NodeId, T> DepthFirstTraverse<'a, Id, T> {
    /// Creates a new iterator.
    #[inline]
    #[must_use]
    pub(super) fn with_toplevel(node: &Node<'a, Id, T>) -> Self {
        Self {
            forest: node.forest(),
            traverser: DepthFirstTraverser::with_toplevel(
                node.id().to_internal(),
                node.hierarchy(),
            ),
        }
    }

    /// Returns the next event without advancing the iterator.
    #[must_use]
    pub fn peek(&self) -> Option<DftEvent<Node<'a, Id, T>>> {
        let ev = self.traverser.peek()?;
        Some(DftEvent::from_hierarchy_dft_event(ev, |id| {
            self.forest
                .node(Id::from_internal(id))
                .expect("[consistency] the node must be the part of the tree")
        }))
    }

    /// Returns the backward next event without advancing the iterator.
    #[must_use]
    pub fn peek_back(&self) -> Option<DftEvent<Node<'a, Id, T>>> {
        let ev = self.traverser.peek_back()?;
        Some(DftEvent::from_hierarchy_dft_event(ev, |id| {
            self.forest
                .node(Id::from_internal(id))
                .expect("[consistency] the node must be the part of the tree")
        }))
    }
}

impl<'a, Id: NodeId, T> Iterator for DepthFirstTraverse<'a, Id, T> {
    type Item = DftEvent<Node<'a, Id, T>>;

    fn next(&mut self) -> Option<Self::Item> {
        let ev = self.traverser.next(&self.forest.hierarchy)?;
        Some(DftEvent::from_hierarchy_dft_event(ev, |id| {
            self.forest
                .node(Id::from_internal(id))
                .expect("[consistency] the node must be the part of the tree")
        }))
    }
}

impl<'a, Id: NodeId, T> DoubleEndedIterator for DepthFirstTraverse<'a, Id, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let ev = self.traverser.next_back(&self.forest.hierarchy)?;
        Some(DftEvent::from_hierarchy_dft_event(ev, |id| {
            self.forest
                .node(Id::from_internal(id))
                .expect("[consistency] the node must be the part of the tree")
        }))
    }
}

impl<Id: NodeId, T> iter::FusedIterator for DepthFirstTraverse<'_, Id, T> {}

/// Double-ended iterator for shallow (i.e. limited-depth) depth-first traversal.
///
/// Values returned by an iterator is a pair of a node and the depth.
/// The root node of the iteration is depth 0.
#[derive(Debug, Clone)]
pub struct ShallowDepthFirstTraverse<'a, Id: NodeId, T> {
    /// Forest.
    forest: &'a Forest<Id, T>,
    /// Traverser.
    traverser: ShallowDepthFirstTraverser<Id::Internal>,
}

impl<'a, Id: NodeId, T> ShallowDepthFirstTraverse<'a, Id, T> {
    /// Creates a new iterator.
    #[inline]
    #[must_use]
    pub(super) fn with_toplevel_and_max_depth(
        node: &Node<'a, Id, T>,
        max_depth: Option<usize>,
    ) -> Self {
        Self {
            forest: node.forest(),
            traverser: ShallowDepthFirstTraverser::with_toplevel_and_max_depth(
                node.id().to_internal(),
                node.hierarchy(),
                max_depth,
            ),
        }
    }

    /// Returns the allowed max depth, if available.
    #[inline]
    #[must_use]
    pub fn max_depth(&self) -> Option<usize> {
        self.traverser.max_depth()
    }

    /// Returns the next event without advancing the iterator.
    #[must_use]
    pub fn peek(&self) -> Option<(DftEvent<Node<'a, Id, T>>, usize)> {
        let (ev, depth) = self.traverser.peek()?;
        Some((
            DftEvent::from_hierarchy_dft_event(ev, |id| {
                self.forest
                    .node(Id::from_internal(id))
                    .expect("[consistency] the node must be the part of the tree")
            }),
            depth,
        ))
    }

    /// Returns the backward next event without advancing the iterator.
    #[must_use]
    pub fn peek_back(&self) -> Option<(DftEvent<Node<'a, Id, T>>, usize)> {
        let (ev, depth) = self.traverser.peek_back()?;
        Some((
            DftEvent::from_hierarchy_dft_event(ev, |id| {
                self.forest
                    .node(Id::from_internal(id))
                    .expect("[consistency] the node must be the part of the tree")
            }),
            depth,
        ))
    }
}

impl<'a, Id: NodeId, T> Iterator for ShallowDepthFirstTraverse<'a, Id, T> {
    type Item = (DftEvent<Node<'a, Id, T>>, usize);

    fn next(&mut self) -> Option<Self::Item> {
        let (ev, depth) = self.traverser.next(&self.forest.hierarchy)?;
        Some((
            DftEvent::from_hierarchy_dft_event(ev, |id| {
                self.forest
                    .node(Id::from_internal(id))
                    .expect("[consistency] the node must be the part of the tree")
            }),
            depth,
        ))
    }
}

impl<'a, Id: NodeId, T> DoubleEndedIterator for ShallowDepthFirstTraverse<'a, Id, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let (ev, depth) = self.traverser.next_back(&self.forest.hierarchy)?;
        Some((
            DftEvent::from_hierarchy_dft_event(ev, |id| {
                self.forest
                    .node(Id::from_internal(id))
                    .expect("[consistency] the node must be the part of the tree")
            }),
            depth,
        ))
    }
}

impl<Id: NodeId, T> iter::FusedIterator for ShallowDepthFirstTraverse<'_, Id, T> {}

/// Ancestors iterator.
#[derive(Debug, Clone)]
pub struct Ancestors<'a, Id: NodeId, T> {
    /// Forest.
    forest: &'a Forest<Id, T>,
    /// Traverser.
    traverser: AncestorsTraverser<Id::Internal>,
}

impl<'a, Id: NodeId, T> Ancestors<'a, Id, T> {
    /// Creates a new iterator.
    #[inline]
    #[must_use]
    pub(super) fn with_start(node: &Node<'a, Id, T>) -> Self {
        Self {
            forest: node.forest(),
            traverser: AncestorsTraverser::with_start(node.id().to_internal(), node.hierarchy()),
        }
    }

    /// Returns the next event without advancing the iterator.
    #[must_use]
    pub fn peek(&self) -> Option<Node<'a, Id, T>> {
        let id = self.traverser.peek()?;
        let node = self
            .forest
            .node(Id::from_internal(id))
            .expect("[consistency] the node must be the part of the tree");
        Some(node)
    }
}

impl<'a, Id: NodeId, T> Iterator for Ancestors<'a, Id, T> {
    type Item = Node<'a, Id, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let id = self.traverser.next(&self.forest.hierarchy)?;
        let node = self
            .forest
            .node(Id::from_internal(id))
            .expect("[consistency] the node must be the part of the tree");
        Some(node)
    }
}

impl<Id: NodeId, T> iter::FusedIterator for Ancestors<'_, Id, T> {}

/// Double-ended iterator for siblings.
#[derive(Debug, Clone)]
pub struct Siblings<'a, Id: NodeId, T> {
    /// Forest.
    forest: &'a Forest<Id, T>,
    /// Traverser.
    traverser: SiblingsTraverser<Id::Internal>,
}

impl<'a, Id: NodeId, T> Siblings<'a, Id, T> {
    /// Creates a new iterator from a parent.
    #[inline]
    #[must_use]
    pub(super) fn with_parent(parent: &Node<'a, Id, T>) -> Self {
        Self {
            forest: parent.forest(),
            traverser: SiblingsTraverser::with_parent(
                parent.id().to_internal(),
                parent.hierarchy(),
            ),
        }
    }

    /// Creates a new iterator from the first sibling in the range.
    #[inline]
    #[must_use]
    pub(super) fn with_first_sibling(first: &Node<'a, Id, T>) -> Self {
        Self {
            forest: first.forest(),
            traverser: SiblingsTraverser::with_first_sibling(
                first.id().to_internal(),
                first.hierarchy(),
            ),
        }
    }

    /// Creates a new iterator from the last sibling in the range.
    #[inline]
    #[must_use]
    pub(super) fn with_last_sibling(last: &Node<'a, Id, T>) -> Self {
        Self {
            forest: last.forest(),
            traverser: SiblingsTraverser::with_last_sibling(
                last.id().to_internal(),
                last.hierarchy(),
            ),
        }
    }

    /// Returns the next event without advancing the iterator.
    #[must_use]
    pub fn peek(&self) -> Option<Node<'a, Id, T>> {
        let id = self.traverser.peek()?;
        let node = self
            .forest
            .node(Id::from_internal(id))
            .expect("[consistency] the node must be the part of the tree");
        Some(node)
    }

    /// Returns the backward next event without advancing the iterator.
    #[must_use]
    pub fn peek_back(&self) -> Option<Node<'a, Id, T>> {
        let id = self.traverser.peek_back()?;
        let node = self
            .forest
            .node(Id::from_internal(id))
            .expect("[consistency] the node must be the part of the tree");
        Some(node)
    }
}

impl<'a, Id: NodeId, T> Iterator for Siblings<'a, Id, T> {
    type Item = Node<'a, Id, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let id = self.traverser.next(&self.forest.hierarchy)?;
        let node = self
            .forest
            .node(Id::from_internal(id))
            .expect("[consistency] the node must be the part of the tree");
        Some(node)
    }
}

impl<'a, Id: NodeId, T> DoubleEndedIterator for Siblings<'a, Id, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let id = self.traverser.next_back(&self.forest.hierarchy)?;
        let node = self
            .forest
            .node(Id::from_internal(id))
            .expect("[consistency] the node must be the part of the tree");
        Some(node)
    }
}

impl<Id: NodeId, T> iter::FusedIterator for Siblings<'_, Id, T> {}

/// Iterator for breadth-first traversal.
///
/// This iterator does not heap-allocate.
///
/// Note that iterating all nodes will be `O(n^2)` operation in worst case,
/// not `O(n)`.
#[derive(Debug, Clone)]
pub struct BreadthFirstTraverse<'a, Id: NodeId, T> {
    /// Forest.
    forest: &'a Forest<Id, T>,
    /// Traverser.
    traverser: BreadthFirstTraverser<Id::Internal>,
}

impl<'a, Id: NodeId, T> BreadthFirstTraverse<'a, Id, T> {
    /// Creates a new iterator.
    #[inline]
    #[must_use]
    pub(super) fn with_toplevel(node: &Node<'a, Id, T>) -> Self {
        Self {
            forest: node.forest(),
            traverser: BreadthFirstTraverser::with_toplevel(
                node.id().to_internal(),
                node.hierarchy(),
            ),
        }
    }
}

impl<'a, Id: NodeId, T> Iterator for BreadthFirstTraverse<'a, Id, T> {
    type Item = (Node<'a, Id, T>, usize);

    fn next(&mut self) -> Option<Self::Item> {
        let (id, depth) = self.traverser.next(&self.forest.hierarchy)?;
        let node = self
            .forest
            .node(Id::from_internal(id))
            .expect("[consistency] the node must be the part of the tree");

        Some((node, depth))
    }
}

impl<Id: NodeId, T> iter::FusedIterator for BreadthFirstTraverse<'_, Id, T> {}

/// Iterator for breadth-first traversal.
///
/// This iterator heap-allocates, and iterating all nodes is `O(n)` operation.
#[derive(Debug, Clone)]
pub struct AllocatingBreadthFirstTraverse<'a, Id: NodeId, T> {
    /// Forest.
    forest: &'a Forest<Id, T>,
    /// Traverser.
    traverser: AllocatingBreadthFirstTraverser<Id::Internal>,
}

impl<'a, Id: NodeId, T> AllocatingBreadthFirstTraverse<'a, Id, T> {
    /// Creates a new iterator.
    #[inline]
    #[must_use]
    pub(super) fn with_toplevel(node: &Node<'a, Id, T>) -> Self {
        Self {
            forest: node.forest(),
            traverser: AllocatingBreadthFirstTraverser::with_toplevel(
                node.id().to_internal(),
                node.hierarchy(),
            ),
        }
    }

    /// Returns the next event without advancing the iterator.
    #[must_use]
    pub fn peek(&self) -> Option<(Node<'a, Id, T>, usize)> {
        let (id, depth) = self.traverser.peek()?;
        let node = self
            .forest
            .node(Id::from_internal(id))
            .expect("[consistency] the node must be the part of the tree");

        Some((node, depth))
    }
}

impl<'a, Id: NodeId, T> Iterator for AllocatingBreadthFirstTraverse<'a, Id, T> {
    type Item = (Node<'a, Id, T>, usize);

    fn next(&mut self) -> Option<Self::Item> {
        let (id, depth) = self.traverser.next(&self.forest.hierarchy)?;
        let node = self
            .forest
            .node(Id::from_internal(id))
            .expect("[consistency] the node must be the part of the tree");

        Some((node, depth))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.traverser.size_hint()
    }
}

impl<Id: NodeId, T> iter::FusedIterator for AllocatingBreadthFirstTraverse<'_, Id, T> {}
