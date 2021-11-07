//! Node ID.

use core::fmt;
use core::hash::Hash;

use crate::nonmax::NonMaxUsize;

/// A trait for internal node ID types.
pub trait InternalNodeId: Copy + Eq + Hash + fmt::Debug + private::Sealed {
    /// Returns the raw `usize` value.
    ///
    /// Note that this is not intended to be implemented on downstream crates.
    fn to_usize(self) -> usize;
    /// Creates a node ID from the raw `usize` value.
    ///
    /// This should return `None` when the node ID creation fails.
    ///
    /// Note that this is not intended to be implemented on downstream crates.
    fn from_usize(v: usize) -> Option<Self>;
}

/// A trait for node ID types.
pub trait NodeId: Copy + Eq + Hash + fmt::Debug {
    /// Internal (backend) node ID type.
    type Internal: InternalNodeId;

    /// Converts the custom ID type to the internal node ID type.
    #[must_use]
    fn from_internal(id: Self::Internal) -> Self;
    /// Converts the internal node ID type to the custom ID type.
    #[must_use]
    fn to_internal(self) -> Self::Internal;
}

impl<T: InternalNodeId> NodeId for T {
    type Internal = Self;

    #[inline]
    fn from_internal(id: Self::Internal) -> Self {
        id
    }
    #[inline]
    fn to_internal(self) -> Self::Internal {
        self
    }
}

/// Implements `NodeId` trait for the given node ID type.
///
/// # Examples
///
/// ```
/// use treena::impl_dynamic_node_id;
/// use treena::dynamic::NodeIdUsize;
///
/// // Tuple struct.
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// pub struct MyId(NodeIdUsize);
/// impl_dynamic_node_id!(MyId, NodeIdUsize, 0);
///
/// // Struct.
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// pub struct MyId2 {
///     underlying: NodeIdUsize,
/// };
/// impl_dynamic_node_id!(MyId2, NodeIdUsize, underlying);
/// ```
#[macro_export]
macro_rules! impl_dynamic_node_id {
    ($outer:ty, $internal:ty, $field:tt) => {
        impl $crate::dynamic::NodeId for $outer {
            type Internal = $internal;

            #[inline]
            fn from_internal(id: Self::Internal) -> Self {
                Self { $field: id }
            }
            #[inline]
            fn to_internal(self) -> Self::Internal {
                self.$field
            }
        }
    };
}

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
pub struct NodeIdUsize(NonMaxUsize);

impl NodeIdUsize {
    /// Returns the raw `usize` value.
    #[inline]
    #[must_use]
    pub(crate) const fn to_usize(self) -> usize {
        self.0.get()
    }
}

// Prevent `{:#?}` from printing the value in redundant 3 lines.
impl fmt::Debug for NodeIdUsize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NodeId({:?})", self.0)
    }
}

impl InternalNodeId for NodeIdUsize {
    #[inline]
    #[must_use]
    fn to_usize(self) -> usize {
        self.0.get()
    }

    #[inline]
    #[must_use]
    fn from_usize(v: usize) -> Option<Self> {
        NonMaxUsize::new(v).map(Self)
    }
}

impl private::Sealed for NodeIdUsize {}

/// Private module to provide [`Sealed`][`private::Sealed`] trait.
mod private {
    /// Trait to prohibit [`InternalNodeId`][`super::InternalNodeId`] trait
    /// implementation by downstream crates.
    pub trait Sealed {}
}

#[cfg(test)]
mod tests {
    use super::*;

    use core::mem;

    #[test]
    fn niche_optimized() {
        assert_eq!(
            mem::size_of::<NodeIdUsize>(),
            mem::size_of::<Option<NodeIdUsize>>(),
            "`Option<NodeId>` type must have the same size as \
             `NodeId` type due to niche optimization"
        );
    }
}
