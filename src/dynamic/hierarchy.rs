//! Dynamic hierarchy for trees and forests.

pub(crate) mod traverse;

use core::fmt;

use alloc::vec::Vec;

use crate::dynamic::forest::StructureError;
use crate::dynamic::{InsertAs, InternalNodeId};

/// A forest without custom data tied to nodes.
#[derive(Debug, Clone)]
pub(crate) struct Hierarchy<Id> {
    /// Neighbors storage.
    neighbors: Vec<Neighbors<Id>>,
}

impl<Id: InternalNodeId> Hierarchy<Id> {
    /// Creates a new root node.
    ///
    /// # Panics
    ///
    /// Panics if the node ID overflows.
    pub(crate) fn create_root(&mut self) -> Id {
        let new_id = Id::from_usize(self.neighbors.len())
            .expect("[precondition] node ID overflowed presumably due to too many node creations");
        self.neighbors.push(Neighbors::new_root(new_id));

        new_id
    }

    /// Returns a reference to the neighbors for the node if the node is alive.
    ///
    /// Returns `None` if the node ID is invalid or the node has already been removed.
    #[must_use]
    pub(crate) fn neighbors(&self, id: Id) -> Option<&Neighbors<Id>> {
        self.neighbors.get(id.to_usize()).filter(|v| v.is_alive())
    }

    /// Returns a mutable reference to the neighbors for the node if the node is alive.
    ///
    /// Returns `None` if the node ID is invalid or the node has already been removed.
    #[must_use]
    pub(crate) fn neighbors_mut(&mut self, id: Id) -> Option<&mut Neighbors<Id>> {
        self.neighbors
            .get_mut(id.to_usize())
            .filter(|v| v.is_alive())
    }

    /// Returns true if the ID is valid inside this forest.
    #[must_use]
    pub(crate) fn is_valid(&self, id: Id) -> bool {
        id.to_usize() < self.neighbors.len()
    }

    /// Returns true if the node is alive.
    #[must_use]
    pub(crate) fn is_alive(&self, id: Id) -> bool {
        self.neighbors
            .get(id.to_usize())
            .map_or(false, |v| v.is_alive())
    }

    /// Connects the given adjacent neighbors and updates fields properly.
    ///
    /// This function connects the given three nodes and update fields to make
    /// them consistent.
    ///
    /// ```text
    ///    parent
    ///     /  \
    ///    /    \
    /// prev -> next
    /// ```
    ///
    /// More precisely, the fields below will be updated:
    ///
    /// * `parent->first_child`,
    ///     + Updated if `prev_child` is `None`, i.e. when `next_child` will be
    ///       the first child or the parent have no child.
    /// * `prev_child->parent`,
    /// * `prev_child->next_sibling`,
    /// * `next_child->parent`, and
    /// * `next_child->prev_sibling_cyclic`.
    ///     + `prev_sibling` is used if available.
    ///     + If `next_child` will be the first child of the parent, the last
    ///       child is used.
    ///     + Otherwise (if both `prev_sibling` and `parent` is `None`),
    ///       `next_child` is used since this means that `next_child` is the
    ///       root of a tree.
    ///
    /// In order to update `prev_sibling_cyclic` of the first sibling,
    /// **nodes should be connected in order** and the last node should be
    /// updated at last.
    ///
    /// # Panics
    ///
    /// * Panics if the `parent` is `None` while both of `prev_child` and
    ///   `next_child` are `Some`, since nodes cannot have siblings without
    ///   having a parent.
    /// * Panics if `prev_child` and `next_child` are both `Some(_)` and are
    ///   identical, since a node cannot be adjacent sibling of itself.
    fn connect_triangle(
        &mut self,
        parent: Option<Id>,
        prev_child: Option<Id>,
        next_child: Option<Id>,
    ) {
        if parent.is_none() && prev_child.is_some() && next_child.is_some() {
            panic!("[precondition] nodes cannot have siblings without having a parent");
        }
        if prev_child
            .zip(next_child)
            .map_or(false, |(prev, next)| prev == next)
        {
            panic!("[precondition] a node cannot be adjacent sibling of itself");
        }

        if let Some(prev_child) = prev_child {
            let prev_child_nbs = self
                .neighbors_mut(prev_child)
                .expect("[precondition] the given `prev_child` node must be alive");
            // Set prev->parent.
            prev_child_nbs.parent = parent;
            // Set prev->next.
            prev_child_nbs.next_sibling = next_child;
        }

        if let Some(next_child) = next_child {
            let next_child_prev_cyclic = match prev_child {
                // If the real previous child exist, just use it.
                Some(prev_child) => prev_child,
                None => match parent {
                    // If `prev_child` is `None` but the parent is available,
                    // then `next_child` is the first child, and
                    // `prev_sibling_cyclic` should be the last child of the
                    // parent.
                    // If the parent does not have any children, then
                    // `next_child` will be the first child.
                    Some(parent) => self
                        .neighbors(parent)
                        .expect("[precondition] the given `parent` node must be alive")
                        .last_child(self)
                        .unwrap_or(next_child),
                    // `next_child` is a root of the tree.
                    None => next_child,
                },
            };

            let next_child_nbs = self
                .neighbors_mut(next_child)
                .expect("[precondition] the given `next_child` node must be alive");
            // Set next->parent.
            next_child_nbs.parent = parent;
            // Set next->prev.
            next_child_nbs.prev_sibling_cyclic = Some(next_child_prev_cyclic);
        }

        // Neighbors of the parent must be modified after `next_child`, since
        // setting `next_child` requires last child of the non-modified parent.
        if let Some(parent) = parent {
            if prev_child.is_none() {
                let parent_nbs = self
                    .neighbors_mut(parent)
                    .expect("[precondition] the given `parent` node must be alive");
                // `next_child` is the first child (if available).
                parent_nbs.first_child = next_child;
            } else if next_child.is_none() {
                // `prev_child` has no next sibling. This means that
                // `prev_child` is the last child of the parent.
                let first_child = self
                    .neighbors(parent)
                    .expect("[precondition] the given `parent` node must be alive")
                    .first_child()
                    .expect("[consistency] `parent` must have a child including `prev_child`");
                if let Some(prev_child) = prev_child {
                    self.neighbors_mut(first_child)
                        .expect("[precondition] the first child of the `parent` must be alive")
                        .prev_sibling_cyclic = Some(prev_child);
                }
            }
        }
    }

    /// Detaches the tree from neighbors.
    ///
    /// Tree structure under the given node will be preserved.
    /// The detached node will become a root node.
    ///
    /// If you want to detach not subtree but single node, use
    /// [`detach_single`][`Self::detach_single`] method.
    ///
    /// ```text
    /// Before `detach`:
    ///
    /// root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2
    ///
    /// After `detach`:
    ///
    /// root
    /// |-- 0
    /// `-- 2
    ///
    /// 1
    /// |-- 1-0
    /// |-- 1-1
    /// `-- 1-2
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
    pub(crate) fn detach(&mut self, node: Id) {
        let nbs = self
            .neighbors(node)
            .expect("[precondition] the node must be alive");
        // If the node has no parent, the tree can be considered already detached.
        let parent = match nbs.parent() {
            Some(v) => v,
            None => return,
        };
        let prev = nbs.prev_sibling(self);
        let next = nbs.next_sibling();

        // Connect the siblings before and after the node.
        self.connect_triangle(Some(parent), prev, next);

        // Reset the neighbors info of the node.
        let mut nbs = self
            .neighbors_mut(node)
            .expect("[precondition] the node must be alive");
        nbs.parent = None;
        nbs.next_sibling = None;
        nbs.prev_sibling_cyclic = Some(node);
    }

    /// Detaches the node from neighbors and make it orphan root.
    ///
    /// Children are inserted to the place where the detached node was.
    ///
    /// If you want to detach not single node but subtree, use
    /// [`detach`][`Self::detach`] method.
    ///
    /// ```text
    /// Before `detach_single`:
    ///
    /// root
    /// |-- 0
    /// |-- 1
    /// |   |-- 1-0
    /// |   |-- 1-1
    /// |   `-- 1-2
    /// `-- 2
    ///
    /// After `detach_single`:
    ///
    /// root
    /// |-- 0
    /// |-- 1-0
    /// |-- 1-1
    /// |-- 1-2
    /// `-- 2
    ///
    /// 1
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`StructureError::SiblingsWithoutParent`] when the node has
    /// multiple children but has no parent.
    ///
    /// # Panics
    ///
    /// Panics if the node is not alive.
    pub(crate) fn detach_single(&mut self, node: Id) -> Result<(), StructureError> {
        let nbs = self
            .neighbors(node)
            .expect("[precondition] the node must be alive");

        let (first_child, last_child) = match nbs.first_last_child(self) {
            Some(v) => v,
            None => {
                // No children.
                self.detach(node);
                return Ok(());
            }
        };

        let parent = match nbs.parent() {
            Some(v) => v,
            None => {
                if first_child != last_child {
                    return Err(StructureError::SiblingsWithoutParent);
                }
                // Single child and no parent.
                // The single child becomes the new root.
                self.detach(first_child);
                // Now the node has no children.
                self.detach(node);
                return Ok(());
            }
        };

        let prev = nbs.prev_sibling(self);
        let next = nbs.next_sibling();

        // Connect the siblings before and after the node.
        self.connect_triangle(Some(parent), prev, next);

        // Insert the children between the prev and next siblings.
        SiblingsRange::new(self, first_child, last_child)
            .transplant(self, parent, prev, next)
            .expect("[consistency] structure being created must be valid");

        // Reset the neighbors info of the node.
        let mut nbs = self
            .neighbors_mut(node)
            .expect("[precondition] the node must be alive");
        nbs.parent = None;
        nbs.next_sibling = None;
        nbs.prev_sibling_cyclic = Some(node);
        debug_assert_eq!(
            nbs.first_child(),
            None,
            "[consistency] the children have been transplanted"
        );

        Ok(())
    }

    /// Detaches `node` and inserts the given node to the target position.
    ///
    /// # Panics
    ///
    /// Panics if any of the given nodes (including the anchor of the destination)
    /// are not alive.
    ///
    /// # Errors
    ///
    /// * [`StructureError::AncestorDescendantLoop`]
    ///     + In case `dest` is `FirstChildOf(node)` or `LastChildOf(node)`.
    /// * [`StructureError::UnorderableSiblings`]
    ///     + In case `dest` is `PreviousSiblingOf(node)` or `NextSiblingOf(node)`.
    /// * [`StructureError::SiblingsWithoutParent`]
    ///     + In case `dest` is `PreviousSiblingOf(v)` or `NextSiblingOf(v)`, and
    ///       `v` does not have a parent.
    pub(crate) fn insert(&mut self, node: Id, dest: InsertAs<Id>) -> Result<(), StructureError> {
        match dest {
            InsertAs::FirstChildOf(parent) => self.prepend_child(node, parent),
            InsertAs::LastChildOf(parent) => self.append_child(node, parent),
            InsertAs::PreviousSiblingOf(next) => self.insert_before(node, next),
            InsertAs::NextSiblingOf(prev) => self.insert_after(node, prev),
        }
    }

    /// Detaches and prepends the given node to children of `self` as the first child.
    ///
    /// # Errors
    ///
    /// Returns [`StructureError::AncestorDescendantLoop`] error when
    /// `new_first_child` and `parent` are identical.
    ///
    /// # Panics
    ///
    /// Panics if any of the given nodes are not alive.
    /// Panics if the `new_first_child` does not have a parent.
    fn prepend_child(&mut self, new_first_child: Id, parent: Id) -> Result<(), StructureError> {
        let old_first_child = self
            .neighbors(parent)
            .expect("[precondition] the node must be alive")
            .first_child();
        SiblingsRange::with_single_toplevel(self, new_first_child).transplant(
            self,
            parent,
            None,
            old_first_child,
        )
    }

    /// Detaches and appends the given node to children of `self` as the last child.
    ///
    /// # Errors
    ///
    /// Returns [`StructureError::AncestorDescendantLoop`] error when
    /// `new_last_child` and `parent` are identical.
    ///
    /// # Panics
    ///
    /// Panics if any of the given nodes are not alive.
    /// Panics if the `new_last_child` does not have a parent.
    fn append_child(&mut self, new_last_child: Id, parent: Id) -> Result<(), StructureError> {
        let old_last_child = self
            .neighbors(parent)
            .expect("[precondition] the parent must be alive")
            .last_child(self);
        // `new_last_child` is an independent tree, so transplanting won't fail.
        SiblingsRange::with_single_toplevel(self, new_last_child).transplant(
            self,
            parent,
            old_last_child,
            None,
        )
    }

    /// Detaches and inserts the given node as the previous sibling of `next_sibling`.
    ///
    /// # Errors
    ///
    /// Returns [`StructureError::UnorderableSiblings`] error when `node` and
    /// `next_sibling` are identical.
    ///
    /// # Panics
    ///
    /// Panics if any of the given nodes are not alive.
    /// Panics if the `next_sibling` does not have a parent.
    fn insert_before(&mut self, node: Id, next_sibling: Id) -> Result<(), StructureError> {
        if node == next_sibling {
            return Err(StructureError::UnorderableSiblings);
        }

        let next_nbs = self
            .neighbors(next_sibling)
            .expect("[precondition] the next sibling must be alive");
        let parent = next_nbs
            .parent()
            .expect("[precondition] the parent must be alive to have siblings");
        let prev_sibling = next_nbs.prev_sibling(self);
        SiblingsRange::with_single_toplevel(self, node).transplant(
            self,
            parent,
            prev_sibling,
            Some(next_sibling),
        )
    }

    /// Detaches and inserts the given node as the next sibling of `prev_sibling`.
    ///
    /// # Errors
    ///
    /// Returns [`StructureError::UnorderableSiblings`] error when `node` and
    /// `prev_sibling` are identical.
    ///
    /// # Panics
    ///
    /// Panics if any of the given nodes are not alive.
    /// Panics if the `prev_sibling` does not have a parent.
    fn insert_after(&mut self, node: Id, prev_sibling: Id) -> Result<(), StructureError> {
        if node == prev_sibling {
            return Err(StructureError::UnorderableSiblings);
        }

        let prev_nbs = self
            .neighbors(prev_sibling)
            .expect("[precondition] the previous sibling must be alive");
        let parent = prev_nbs
            .parent()
            .expect("[precondition] the parent must be alive to have siblings");
        let next_sibling = prev_nbs.next_sibling();
        SiblingsRange::with_single_toplevel(self, node).transplant(
            self,
            parent,
            Some(prev_sibling),
            next_sibling,
        )
    }
}

impl<Id: InternalNodeId> Default for Hierarchy<Id> {
    #[inline]
    fn default() -> Self {
        Self {
            neighbors: Default::default(),
        }
    }
}

/// Neighbors.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct Neighbors<Id> {
    /// Parent.
    parent: Option<Id>,
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
    prev_sibling_cyclic: Option<Id>,
    /// Next sibling.
    next_sibling: Option<Id>,
    /// First child.
    first_child: Option<Id>,
}

impl<Id: InternalNodeId> Neighbors<Id> {
    /// Creates a new `Neighbors` that is not connected to anyone.
    #[inline]
    #[must_use]
    fn new_root(id: Id) -> Self {
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
    pub(crate) fn parent(&self) -> Option<Id> {
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
    pub(crate) fn next_sibling(&self) -> Option<Id> {
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
    pub(crate) fn prev_sibling(&self, hier: &Hierarchy<Id>) -> Option<Id> {
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
    pub(crate) fn first_child(&self) -> Option<Id> {
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
    pub(crate) fn last_child(&self, hier: &Hierarchy<Id>) -> Option<Id> {
        self.first_last_child(hier).map(|(_first, last)| last)
    }

    /// Returns the node IDs of the first child and the last child.
    ///
    /// # Panics
    ///
    /// Panics if the `self` node has already been removed.
    #[inline]
    #[must_use]
    pub(crate) fn first_last_child(&self, hier: &Hierarchy<Id>) -> Option<(Id, Id)> {
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

    /// Returns true if the node has no neighbors.
    ///
    /// # Panics
    ///
    /// Panics if the `self` node has already been removed.
    #[must_use]
    pub(crate) fn is_alone(&self) -> bool {
        if !self.is_alive() {
            panic!("[precondition] the node must be alive");
        }
        self.parent.is_none() && self.next_sibling.is_none() && self.first_child.is_none()
    }

    /// Makes the node removed state.
    ///
    /// It is caller's responsibility to make the node alone and keep the
    /// hierarchy consistent.
    ///
    /// # Panics
    ///
    /// Panics if the `self` node has already been removed.
    /// Panics if the `self` node is not alone.
    pub(crate) fn make_removed(&mut self) {
        if !self.is_alone() {
            panic!("[precondition] the node must be alive and alone");
        }
        self.force_make_removed();
    }

    /// Makes the node removed state **even if it can make the arena inconsistent**.
    ///
    /// It is caller's responsibility to make the node alone and/or make the
    /// hierarchy finally consistent.
    ///
    /// # Panics
    ///
    /// Panics if the `self` node has already been removed.
    pub(crate) fn force_make_removed(&mut self) {
        if !self.is_alive() {
            panic!("[precondition] the node must be alive");
        }
        self.parent = None;
        self.prev_sibling_cyclic = None;
        self.next_sibling = None;
        self.first_child = None;
    }
}

// For compact printing.
impl<Id: fmt::Debug> fmt::Debug for Neighbors<Id> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        /// A wrapper to print optional node ID in compact form.
        #[derive(Clone, Copy)]
        struct OptNodeId<'a, Id>(&'a Option<Id>);
        impl<Id: fmt::Debug> fmt::Debug for OptNodeId<'_, Id> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self.0 {
                    Some(id) => id.fmt(f),
                    None => f.write_str("None"),
                }
            }
        }

        f.debug_struct("Neighbors")
            .field("parent", &OptNodeId(&self.parent))
            .field("prev_sibling_cyclic", &OptNodeId(&self.prev_sibling_cyclic))
            .field("next_sibling", &OptNodeId(&self.next_sibling))
            .field("first_child", &OptNodeId(&self.first_child))
            .finish()
    }
}

/// Siblings range.
#[derive(Debug)]
struct SiblingsRange<Id> {
    /// First node in the range.
    first: Id,
    /// Last node in the range.
    last: Id,
}

impl<Id: InternalNodeId> SiblingsRange<Id> {
    /// Creates a new siblings range.
    ///
    /// # Panics
    ///
    /// * Panics if `first` or `last` is not alive.
    /// * Panics if `first` and `last` does not have the same parent node.
    // TODO: Ordering:
    // This should panic if `first` is a succeeding sibling of `prev`.
    // However, this won't be O(1) operation. The hierarchy does not have an
    // efficient way to test siblings orders.
    // Without testing this, the function should be considered as unsafe.
    // For now, it is caller's responsibility to ensure siblings order.
    fn new(hier: &Hierarchy<Id>, first: Id, last: Id) -> Self {
        if first == last {
            return Self::with_single_toplevel(hier, first);
        }

        let first_parent = hier
            .neighbors(first)
            .expect("[precondition] `first` node must be alive")
            .parent();
        let last_parent = hier
            .neighbors(last)
            .expect("[precondition] `last` node must be alive")
            .parent();
        if first_parent != last_parent {
            panic!("[precondition] `first` and `last` must have the same parent");
        }

        Self { first, last }
    }

    /// Creates a new siblings range from a single toplevel node.
    ///
    /// # Panics
    ///
    /// * Panics if the node is not alive.
    fn with_single_toplevel(hier: &Hierarchy<Id>, node: Id) -> Self {
        if !hier.is_alive(node) {
            panic!("[precondition] the node must be alive");
        }

        Self {
            first: node,
            last: node,
        }
    }

    /// Inserts the nodes in the range to the given place.
    ///
    /// ```text
    /// Before:
    ///
    ///            parent
    ///             /  \
    ///            /    \
    /// prev_sibling -> next_sibling
    ///
    ///                       (possible parent)
    ///             _____________/ __/ \___ \______________
    ///            /              /        \                \
    /// PREV_OF_FIRST -> self.first --...-> self.last -> NEXT_OF_LAST
    ///
    ///
    /// After:
    ///
    ///                             parent
    ///             _____________/ __/ \___ \______________
    ///            /              /        \                \
    /// prev_sibling -> self.first --...-> self.last -> next_sibling
    ///
    ///        (possible parent)
    ///              /  \
    ///             /    \
    /// PREV_OF_FIRST -> NEXT_OF_LAST
    /// ```
    ///
    /// # Panics
    ///
    /// * Panics if the `parent`, `prev_sibling`, or `next_sibling` is not alive.
    /// * Panics if the `parent` is not the actual parent of `prev_sibling` and
    ///   `next_sibling`.
    /// * Panics if any node in the range (`self`) is not alive.
    fn transplant(
        self,
        hier: &mut Hierarchy<Id>,
        parent: Id,
        prev_sibling: Option<Id>,
        next_sibling: Option<Id>,
    ) -> Result<(), StructureError> {
        // Detach the nodes.
        {
            let first_nbs = hier
                .neighbors(self.first)
                .expect("[consistency] nodes in the range must be alive");
            let range_parent = first_nbs.parent();
            let prev_of_range = first_nbs.prev_sibling(hier);
            let next_of_range = hier
                .neighbors(self.last)
                .expect("[consistency] nodes in the range must be alive")
                .next_sibling();
            // Connect the nodes before and after the range.
            hier.connect_triangle(range_parent, prev_of_range, next_of_range);
        }

        // Rewrite parents in the range.
        {
            let mut child_opt = Some(self.first);
            while let Some(child) = child_opt {
                if child == parent {
                    return Err(StructureError::AncestorDescendantLoop);
                }
                let child_nbs = hier
                    .neighbors_mut(child)
                    .expect("[consistency] nodes in the range must be alive");
                child_nbs.parent = Some(parent);
                if child == self.last {
                    break;
                }
                child_opt = child_nbs.next_sibling();
            }
        }

        // Connect the first node in the range to the previous sibling.
        // If they are identical, no need to update neighbors info.
        if prev_sibling != Some(self.first) {
            hier.connect_triangle(Some(parent), prev_sibling, Some(self.first));
        }

        // Connect the last node in the range to the next sibling.
        // If they are identical, no need to update neighbors info.
        if next_sibling != Some(self.last) {
            hier.connect_triangle(Some(parent), Some(self.last), next_sibling);
        }

        Ok(())
    }
}
