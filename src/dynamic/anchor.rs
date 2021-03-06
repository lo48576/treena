//! Anchors.

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
    pub(super) fn insert_with_anchor<Id>(self, anchor: Id) -> InsertAs<Id> {
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
pub enum InsertAs<Id> {
    /// As the first child.
    FirstChildOf(Id),
    /// As the last child.
    LastChildOf(Id),
    /// As the previous sibling.
    PreviousSiblingOf(Id),
    /// As the next sibling.
    NextSiblingOf(Id),
}

impl<Id> InsertAs<Id> {
    /// Converts the ID type.
    pub(super) fn map<U, F>(self, f: F) -> InsertAs<U>
    where
        F: FnOnce(Id) -> U,
    {
        match self {
            Self::FirstChildOf(id) => InsertAs::FirstChildOf(f(id)),
            Self::LastChildOf(id) => InsertAs::LastChildOf(f(id)),
            Self::PreviousSiblingOf(id) => InsertAs::PreviousSiblingOf(f(id)),
            Self::NextSiblingOf(id) => InsertAs::NextSiblingOf(f(id)),
        }
    }

    /// Returns the anchor.
    ///
    /// This is only intended for internal use, so assumes the `Id` implement `Copy`.
    pub(super) fn to_anchor(self) -> Id
    where
        Id: Copy,
    {
        match self {
            Self::FirstChildOf(id) => id,
            Self::LastChildOf(id) => id,
            Self::PreviousSiblingOf(id) => id,
            Self::NextSiblingOf(id) => id,
        }
    }
}
