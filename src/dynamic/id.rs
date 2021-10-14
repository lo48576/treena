//! Node ID.

use core::fmt;

use crate::nonmax::NonMaxUsize;

/// Node ID.
///
/// The ordering (`PartialOrd` and `Ord`) for node IDs are only provided for
/// use with some containers who wants ordered key types (such as `BTreeSet`).
/// Note that it is **not** guaranteed that the ordering of a key has some
/// relation to the order the node is created.
/// This also means that the users must use `Debug` formatting only for dumping
/// the value, but not for manipulating internal integer value extracted by
/// `Debug` trait.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeId(NonMaxUsize);

impl NodeId {
    /// Returns the raw `usize` value.
    #[inline]
    #[must_use]
    pub(crate) const fn get(self) -> usize {
        self.0.get()
    }

    /// Creates a node ID from the raw `usize` value.
    ///
    /// Returns `None` if the given value is too large.
    #[inline]
    #[must_use]
    pub(crate) fn from_usize(v: usize) -> Option<Self> {
        NonMaxUsize::new(v).map(Self)
    }
}

// Prevent `{:#?}` from printing the value in redundant 3 lines.
impl fmt::Debug for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NodeId({:?})", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use core::mem;

    #[test]
    fn niche_optimized() {
        assert_eq!(
            mem::size_of::<NodeId>(),
            mem::size_of::<Option<NodeId>>(),
            "`Option<NodeId>` type must have the same size as \
             `NodeId` type due to niche optimization"
        );
    }
}
