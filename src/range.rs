#![doc(hidden)]

use core::fmt::Display;

/// Represents a range of bytes in
/// [`AllocationTracker`](crate::tracker::AllocationTracker) and
/// [`ContiguousMemoryStorage`](crate::ContiguousMemoryStorage).
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

    /// Aligns this byte range to the provided `alignment`.
    pub fn aligned(&self, alignment: usize) -> Self {
        let modulo = self.0 % alignment;
        if modulo == 0 {
            return *self;
        }
        self.offset(alignment - modulo)
    }

    /// Caps the end address of this byte range to the provided `position`.
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
    pub fn len(&self) -> usize {
        self.1 - self.0
    }

    /// Returns `true` if this byte range contains another byte range `other`.
    pub fn contains(&self, other: Self) -> bool {
        self.0 <= other.0 && other.1 <= self.1
    }

    /// Returns two byte ranges that remain when another `other` range is
    /// removed from this one.
    ///
    /// It is possible for either or both of the returned byte ranges to have a
    /// length of 0 if `other` is aligned with either the upper or lower bound
    /// of this range, or if it is equal to this range.
    pub fn difference_unchecked(&self, other: Self) -> (Self, Self) {
        (ByteRange(self.0, other.0), ByteRange(other.1, self.1))
    }

    /// Merges this byte range with `other` and returns a byte range that
    /// contains both.
    pub fn merge_unchecked(&self, other: Self) -> Self {
        ByteRange(self.0.min(other.0), self.1.max(other.1))
    }

    /// Merges another `other` byte range into this one, resulting in a byte
    /// range that contains both.
    pub fn merge_in_unchecked(&mut self, other: Self) {
        self.0 = self.0.min(other.0);
        self.1 = self.1.max(other.1);
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

        let added_seq = a.merge_unchecked(b);
        assert_eq!(added_seq.0, 0);
        assert_eq!(added_seq.1, 20);

        let added_seq_rev = b.merge_unchecked(a);
        assert_eq!(added_seq_rev.0, 0);
        assert_eq!(added_seq_rev.1, 20);
    }

    #[test]
    fn byterange_difference_works() {
        let larger = ByteRange::new_unchecked(0, 500);

        let left_aligned = ByteRange::new_unchecked(0, 10);
        let test_left = larger.difference_unchecked(left_aligned);
        assert_eq!(test_left.0 .0, 0);
        assert_eq!(test_left.0 .1, 0);
        assert_eq!(test_left.1 .0, 10);
        assert_eq!(test_left.1 .1, 500);

        let contained = ByteRange::new_unchecked(300, 400);
        let test_contained = larger.difference_unchecked(contained);
        assert_eq!(test_contained.0 .0, 0);
        assert_eq!(test_contained.0 .1, 300);
        assert_eq!(test_contained.1 .0, 400);
        assert_eq!(test_contained.1 .1, 500);

        let right_aligned = ByteRange::new_unchecked(450, 500);
        let test_right = larger.difference_unchecked(right_aligned);
        assert_eq!(test_right.0 .0, 0);
        assert_eq!(test_right.0 .1, 450);
        assert_eq!(test_right.1 .0, 500);
        assert_eq!(test_right.1 .1, 500);
    }
}
