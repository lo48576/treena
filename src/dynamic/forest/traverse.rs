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
    fn from_hierarchy_dft_event<F>(ev: DftEventSrc, f: F) -> Self
    where
        F: FnOnce(NodeId) -> T,
    {
        match ev {
            DftEventSrc::Open(v) => Self::Open(f(v)),
            DftEventSrc::Close(v) => Self::Close(f(v)),
        }
    }
}

/// Double-ended iterator for depth-first traversal.
#[derive(Debug, Clone)]
pub struct DepthFirstTraverse<'a, T> {
    /// Forest.
    forest: &'a Forest<T>,
    /// Traverser.
    traverser: DepthFirstTraverser,
}

impl<'a, T> DepthFirstTraverse<'a, T> {
    /// Creates a new iterator.
    #[inline]
    #[must_use]
    pub(super) fn with_toplevel(node: &Node<'a, T>) -> Self {
        Self {
            forest: node.forest(),
            traverser: DepthFirstTraverser::with_toplevel(node.id(), node.hierarchy()),
        }
    }

    /// Returns the next event without advancing the iterator.
    #[must_use]
    pub fn peek(&self) -> Option<DftEvent<Node<'a, T>>> {
        let ev = self.traverser.peek()?;
        Some(DftEvent::from_hierarchy_dft_event(ev, |id| {
            self.forest
                .node(id)
                .expect("[consistency] the node must be the part of the tree")
        }))
    }

    /// Returns the backward next event without advancing the iterator.
    #[must_use]
    pub fn peek_back(&self) -> Option<DftEvent<Node<'a, T>>> {
        let ev = self.traverser.peek_back()?;
        Some(DftEvent::from_hierarchy_dft_event(ev, |id| {
            self.forest
                .node(id)
                .expect("[consistency] the node must be the part of the tree")
        }))
    }
}

impl<'a, T> Iterator for DepthFirstTraverse<'a, T> {
    type Item = DftEvent<Node<'a, T>>;

    fn next(&mut self) -> Option<Self::Item> {
        let ev = self.traverser.next(&self.forest.hierarchy)?;
        Some(DftEvent::from_hierarchy_dft_event(ev, |id| {
            self.forest
                .node(id)
                .expect("[consistency] the node must be the part of the tree")
        }))
    }
}

impl<'a, T> DoubleEndedIterator for DepthFirstTraverse<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let ev = self.traverser.next_back(&self.forest.hierarchy)?;
        Some(DftEvent::from_hierarchy_dft_event(ev, |id| {
            self.forest
                .node(id)
                .expect("[consistency] the node must be the part of the tree")
        }))
    }
}

impl<T> iter::FusedIterator for DepthFirstTraverse<'_, T> {}

/// Double-ended iterator for shallow (i.e. limited-depth) depth-first traversal.
///
/// Values returned by an iterator is a pair of a node and the depth.
/// The root node of the iteration is depth 0.
#[derive(Debug, Clone)]
pub struct ShallowDepthFirstTraverse<'a, T> {
    /// Forest.
    forest: &'a Forest<T>,
    /// Traverser.
    traverser: ShallowDepthFirstTraverser,
}

impl<'a, T> ShallowDepthFirstTraverse<'a, T> {
    /// Creates a new iterator.
    #[inline]
    #[must_use]
    pub(super) fn with_toplevel_and_max_depth(
        node: &Node<'a, T>,
        max_depth: Option<usize>,
    ) -> Self {
        Self {
            forest: node.forest(),
            traverser: ShallowDepthFirstTraverser::with_toplevel_and_max_depth(
                node.id(),
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
    pub fn peek(&self) -> Option<(DftEvent<Node<'a, T>>, usize)> {
        let (ev, depth) = self.traverser.peek()?;
        Some((
            DftEvent::from_hierarchy_dft_event(ev, |id| {
                self.forest
                    .node(id)
                    .expect("[consistency] the node must be the part of the tree")
            }),
            depth,
        ))
    }

    /// Returns the backward next event without advancing the iterator.
    #[must_use]
    pub fn peek_back(&self) -> Option<(DftEvent<Node<'a, T>>, usize)> {
        let (ev, depth) = self.traverser.peek_back()?;
        Some((
            DftEvent::from_hierarchy_dft_event(ev, |id| {
                self.forest
                    .node(id)
                    .expect("[consistency] the node must be the part of the tree")
            }),
            depth,
        ))
    }
}

impl<'a, T> Iterator for ShallowDepthFirstTraverse<'a, T> {
    type Item = (DftEvent<Node<'a, T>>, usize);

    fn next(&mut self) -> Option<Self::Item> {
        let (ev, depth) = self.traverser.next(&self.forest.hierarchy)?;
        Some((
            DftEvent::from_hierarchy_dft_event(ev, |id| {
                self.forest
                    .node(id)
                    .expect("[consistency] the node must be the part of the tree")
            }),
            depth,
        ))
    }
}

impl<'a, T> DoubleEndedIterator for ShallowDepthFirstTraverse<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let (ev, depth) = self.traverser.next_back(&self.forest.hierarchy)?;
        Some((
            DftEvent::from_hierarchy_dft_event(ev, |id| {
                self.forest
                    .node(id)
                    .expect("[consistency] the node must be the part of the tree")
            }),
            depth,
        ))
    }
}

impl<T> iter::FusedIterator for ShallowDepthFirstTraverse<'_, T> {}

/// Ancestors iterator.
#[derive(Debug, Clone)]
pub struct Ancestors<'a, T> {
    /// Forest.
    forest: &'a Forest<T>,
    /// Traverser.
    traverser: AncestorsTraverser,
}

impl<'a, T> Ancestors<'a, T> {
    /// Creates a new iterator.
    #[inline]
    #[must_use]
    pub(super) fn with_start(node: &Node<'a, T>) -> Self {
        Self {
            forest: node.forest(),
            traverser: AncestorsTraverser::with_start(node.id(), node.hierarchy()),
        }
    }

    /// Returns the next event without advancing the iterator.
    #[must_use]
    pub fn peek(&self) -> Option<Node<'a, T>> {
        let id = self.traverser.peek()?;
        let node = self
            .forest
            .node(id)
            .expect("[consistency] the node must be the part of the tree");
        Some(node)
    }
}

impl<'a, T> Iterator for Ancestors<'a, T> {
    type Item = Node<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let id = self.traverser.next(&self.forest.hierarchy)?;
        let node = self
            .forest
            .node(id)
            .expect("[consistency] the node must be the part of the tree");
        Some(node)
    }
}

impl<T> iter::FusedIterator for Ancestors<'_, T> {}

/// Double-ended iterator for siblings.
#[derive(Debug, Clone)]
pub struct Siblings<'a, T> {
    /// Forest.
    forest: &'a Forest<T>,
    /// Traverser.
    traverser: SiblingsTraverser,
}

impl<'a, T> Siblings<'a, T> {
    /// Creates a new iterator from a parent.
    #[inline]
    #[must_use]
    pub(super) fn with_parent(parent: &Node<'a, T>) -> Self {
        Self {
            forest: parent.forest(),
            traverser: SiblingsTraverser::with_parent(parent.id(), parent.hierarchy()),
        }
    }

    /// Creates a new iterator from the first sibling in the range.
    #[inline]
    #[must_use]
    pub(super) fn with_first_sibling(first: &Node<'a, T>) -> Self {
        Self {
            forest: first.forest(),
            traverser: SiblingsTraverser::with_first_sibling(first.id(), first.hierarchy()),
        }
    }

    /// Creates a new iterator from the last sibling in the range.
    #[inline]
    #[must_use]
    pub(super) fn with_last_sibling(last: &Node<'a, T>) -> Self {
        Self {
            forest: last.forest(),
            traverser: SiblingsTraverser::with_last_sibling(last.id(), last.hierarchy()),
        }
    }

    /// Returns the next event without advancing the iterator.
    #[must_use]
    pub fn peek(&self) -> Option<Node<'a, T>> {
        let id = self.traverser.peek()?;
        let node = self
            .forest
            .node(id)
            .expect("[consistency] the node must be the part of the tree");
        Some(node)
    }

    /// Returns the backward next event without advancing the iterator.
    #[must_use]
    pub fn peek_back(&self) -> Option<Node<'a, T>> {
        let id = self.traverser.peek_back()?;
        let node = self
            .forest
            .node(id)
            .expect("[consistency] the node must be the part of the tree");
        Some(node)
    }
}

impl<'a, T> Iterator for Siblings<'a, T> {
    type Item = Node<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let id = self.traverser.next(&self.forest.hierarchy)?;
        let node = self
            .forest
            .node(id)
            .expect("[consistency] the node must be the part of the tree");
        Some(node)
    }
}

impl<'a, T> DoubleEndedIterator for Siblings<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let id = self.traverser.next_back(&self.forest.hierarchy)?;
        let node = self
            .forest
            .node(id)
            .expect("[consistency] the node must be the part of the tree");
        Some(node)
    }
}

impl<T> iter::FusedIterator for Siblings<'_, T> {}

/// Iterator for breadth-first traversal.
///
/// This iterator does not heap-allocate.
///
/// Note that iterating all nodes will be `O(n^2)` operation in worst case,
/// not `O(n)`.
#[derive(Debug, Clone)]
pub struct BreadthFirstTraverse<'a, T> {
    /// Forest.
    forest: &'a Forest<T>,
    /// Traverser.
    traverser: BreadthFirstTraverser,
}

impl<'a, T> BreadthFirstTraverse<'a, T> {
    /// Creates a new iterator.
    #[inline]
    #[must_use]
    pub(super) fn with_toplevel(node: &Node<'a, T>) -> Self {
        Self {
            forest: node.forest(),
            traverser: BreadthFirstTraverser::with_toplevel(node.id(), node.hierarchy()),
        }
    }
}

impl<'a, T> Iterator for BreadthFirstTraverse<'a, T> {
    type Item = (Node<'a, T>, usize);

    fn next(&mut self) -> Option<Self::Item> {
        let (id, depth) = self.traverser.next(&self.forest.hierarchy)?;
        let node = self
            .forest
            .node(id)
            .expect("[consistency] the node must be the part of the tree");

        Some((node, depth))
    }
}

impl<T> iter::FusedIterator for BreadthFirstTraverse<'_, T> {}

/// Iterator for breadth-first traversal.
///
/// This iterator heap-allocates, and iterating all nodes is `O(n)` operation.
#[derive(Debug, Clone)]
pub struct AllocatingBreadthFirstTraverse<'a, T> {
    /// Forest.
    forest: &'a Forest<T>,
    /// Traverser.
    traverser: AllocatingBreadthFirstTraverser,
}

impl<'a, T> AllocatingBreadthFirstTraverse<'a, T> {
    /// Creates a new iterator.
    #[inline]
    #[must_use]
    pub(super) fn with_toplevel(node: &Node<'a, T>) -> Self {
        Self {
            forest: node.forest(),
            traverser: AllocatingBreadthFirstTraverser::with_toplevel(node.id(), node.hierarchy()),
        }
    }

    /// Returns the next event without advancing the iterator.
    #[must_use]
    pub fn peek(&self) -> Option<(Node<'a, T>, usize)> {
        let (id, depth) = self.traverser.peek()?;
        let node = self
            .forest
            .node(id)
            .expect("[consistency] the node must be the part of the tree");

        Some((node, depth))
    }
}

impl<'a, T> Iterator for AllocatingBreadthFirstTraverse<'a, T> {
    type Item = (Node<'a, T>, usize);

    fn next(&mut self) -> Option<Self::Item> {
        let (id, depth) = self.traverser.next(&self.forest.hierarchy)?;
        let node = self
            .forest
            .node(id)
            .expect("[consistency] the node must be the part of the tree");

        Some((node, depth))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.traverser.size_hint()
    }
}

impl<T> iter::FusedIterator for AllocatingBreadthFirstTraverse<'_, T> {}
