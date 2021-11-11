//! `NonMaxUsize` for node ID.

use core::cmp::Ordering;
use core::fmt;

/// Implements formatting traits under `core::fmt` for a non-max integer type.
macro_rules! impl_fmt {
    ($ty:ty, $($trait:ident),*) => {
        $(
            impl fmt::$trait for $ty {
                #[inline]
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    self.get().fmt(f)
                }
            }
        )*
    };
}

/// Defines a non-max type and implements necessary traits.
macro_rules! define_type {
    ($ty:ident, $backend:ty, $tyint:ident) => {
        #[doc = concat!("`", stringify!($tyint), "`")]
        ///  that is known not to equal
        #[doc = concat!(" `", stringify!($tyint), "::MAX`")]
        /// .
        ///
        #[doc = concat!("`Option<", stringify!($ty), ">`")]
        ///  is guaranteed to be the same size as
        #[doc = concat!("`", stringify!($ty), "`")]
        ///  itself.
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        #[repr(transparent)]
        pub(crate) struct $ty($backend);

        impl $ty {
            /// Creates a non-max
            #[doc = concat!("`", stringify!($tyint), "`")]
            ///  value.
            #[inline]
            #[must_use]
            pub(crate) fn new(n: usize) -> Option<Self> {
                <$tyint>::try_from(n)
                    .ok()
                    .and_then(|n| <$backend>::new(!n))
                    .map(Self)
            }

            /// Returns the value as a `usize` type value.
            #[inline]
            #[must_use]
            pub(crate) const fn get(self) -> usize {
                // The internal value must be representable by `usize`, since the
                // value should be created from `usize` by `Self::new` method.
                !self.0.get() as usize
            }
        }

        impl Default for $ty {
            fn default() -> Self {
                Self::new(0).expect("[validity] 0 is not the max value of the internal integer")
            }
        }

        impl Ord for $ty {
            #[inline]
            fn cmp(&self, other: &Self) -> Ordering {
                self.0.cmp(&other.0).reverse()
            }
        }

        impl PartialOrd for $ty {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl_fmt!($ty, Debug, Display, Binary, Octal, LowerHex, UpperHex);
    };
}

define_type!(NonMaxUsize, core::num::NonZeroUsize, usize);

#[cfg(test)]
mod tests {
    use super::NonMaxUsize;

    use core::mem::size_of;

    #[test]
    fn types_size() {
        assert_eq!(
            size_of::<NonMaxUsize>(),
            size_of::<usize>(),
            "`NonMaxUsize` should be same size as `usize`"
        );
        assert_eq!(
            size_of::<Option<NonMaxUsize>>(),
            size_of::<NonMaxUsize>(),
            "`Option<NonMaxUsize>` should be same size as `NonMaxUsize`"
        );
    }
}
