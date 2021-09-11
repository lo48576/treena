//! `NonMaxUsize` for node ID.

use core::cmp::Ordering;
use core::fmt;
use core::num::NonZeroUsize;

/// `usize` that is known not to equal `usize::MAX`.
///
/// `Option<NonMaxUsize>` is guaranteed to be the same size as `NonMaxUsize` itself.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub(crate) struct NonMaxUsize(NonZeroUsize);

impl NonMaxUsize {
    /// Creates a non-max usize value.
    #[inline]
    #[must_use]
    pub(crate) const fn new(n: usize) -> Option<Self> {
        // Cannot use `Option<_>::map` here since it is not `const` function.
        match NonZeroUsize::new(!n) {
            Some(v) => Some(Self(v)),
            None => None,
        }
    }

    /// Returns the value as a `usize` type.
    #[inline]
    #[must_use]
    pub(crate) const fn get(self) -> usize {
        !self.0.get()
    }
}

impl Default for NonMaxUsize {
    fn default() -> Self {
        Self::new(0).expect("[validity] 0 is not the max value of the internal integer")
    }
}

impl Ord for NonMaxUsize {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0).reverse()
    }
}

impl PartialOrd for NonMaxUsize {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

macro_rules! impl_fmt {
    ($($trait:ident),*) => {
        $(
            impl fmt::$trait for NonMaxUsize {
                #[inline]
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    self.get().fmt(f)
                }
            }
        )*
    };
}
impl_fmt!(Debug, Display, Binary, Octal, LowerHex, UpperHex);

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
