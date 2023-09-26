//! Contains [`ByteRange`] and related code.

use core::fmt::Display;

use crate::raw::BaseAddress;

/// Represents a range of bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ByteRange(
    /// **Inclusive** lower bound of this byte range.
    pub usize,
    /// **Exclusive** upper bound of this byte range.
    pub usize,
);

impl ByteRange {
    /// Constructs a new byte range, ensuring that `from` and `to` are ordered
    /// correctly.
    pub fn new(from: usize, to: usize) -> Self {
        ByteRange(from.min(to), to.max(from))
    }

    /// Constructs a new byte range without checking `from` and `to` ordering.
    pub fn new_unchecked(from: usize, to: usize) -> Self {
        ByteRange(from, to)
    }

    /// Aligns the start of this byte range to the provided `alignment`.
    pub fn aligned(&self, alignment: usize) -> Self {
        let modulo = self.0 % alignment;
        if modulo == 0 {
            return *self;
        }
        ByteRange(self.0 + alignment - modulo, self.1)
    }

    /// Aligns the start of this byte range to the provided `alignment`.
    pub fn offset_aligned(&self, alignment: usize) -> Self {
        let modulo = self.0 % alignment;
        if modulo == 0 {
            return *self;
        }
        self.offset(alignment - modulo)
    }

    /// Caps the end address of this byte range to the provided `position`.
    #[inline]
    pub fn cap_end(&self, position: usize) -> Self {
        ByteRange(self.0, position.min(self.1))
    }

    /// Caps the size of this byte range to the provided `size`.
    pub fn cap_size(&self, size: usize) -> Self {
        if self.len() < size {
            return *self;
        }
        ByteRange(self.0, self.0 + size)
    }

    /// Offsets this byte range by a provided unsigned `offset`.
    #[inline]
    pub fn offset(&self, offset: usize) -> Self {
        ByteRange(self.0 + offset, self.1 + offset)
    }

    /// Offsets this byte range by a provided signed offset.
    pub fn offset_signed(&self, offset: isize) -> Self {
        ByteRange(
            ((self.0 as isize).wrapping_add(offset)) as usize,
            ((self.1 as isize).wrapping_add(offset)) as usize,
        )
    }

    /// Returns length of this byte range.
    #[inline]
    pub fn len(&self) -> usize {
        self.1 - self.0
    }

    /// Returns true if this byte range is zero-sized.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0 == self.1
    }

    /// Returns `true` if this byte range contains `other` byte range.
    #[inline]
    pub fn contains(&self, other: Self) -> bool {
        self.0 <= other.0 && other.1 <= self.1
    }

    /// Returns `true` if `other` byte range overlaps this byte range.
    #[inline]
    pub fn overlaps(&self, other: Self) -> bool {
        self.contains(other)
            || (other.0 <= self.0 && other.1 > self.0)
            || (other.0 < self.1 && other.1 > self.1)
    }

    /// Merges this byte range with `other` and returns a byte range that
    /// contains both.
    pub fn union_unchecked(&self, other: Self) -> Self {
        ByteRange(self.0.min(other.0), self.1.max(other.1))
    }

    /// Merges another `other` byte range into this one, resulting in a byte
    /// range that contains both.
    pub fn apply_union_unchecked(&mut self, other: Self) {
        self.0 = self.0.min(other.0);
        self.1 = self.1.max(other.1);
    }

    #[inline]
    pub(crate) fn offset_base<T>(&self, addr: BaseAddress) -> Option<*mut T> {
        addr.map(|it| (it.as_ptr() as *mut u8 as usize + self.0) as *mut T)
    }

    #[inline]
    pub(crate) unsafe fn offset_base_unwrap<T>(&self, addr: BaseAddress) -> *mut T {
        (unsafe { addr.unwrap_unchecked().as_ptr() } as *mut u8 as usize + self.0) as *mut T
    }
}

impl Display for ByteRange {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "[{:x}, {:x})", self.0, self.1)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn byterange_merging_works() {
        let a = ByteRange::new_unchecked(0, 10);
        let b = ByteRange::new_unchecked(10, 20);

        let added_seq = a.union_unchecked(b);
        assert_eq!(added_seq.0, 0);
        assert_eq!(added_seq.1, 20);

        let added_seq_rev = b.union_unchecked(a);
        assert_eq!(added_seq_rev.0, 0);
        assert_eq!(added_seq_rev.1, 20);
    }
}
