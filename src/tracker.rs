#![doc(hidden)]

use core::alloc::Layout;

#[cfg(feature = "no_std")]
use crate::types::{vec, Vec};
use crate::{error::AllocationTrackerError, range::ByteRange, raw::BaseAddress};

/// A structure that keeps track of unused regions of memory within provided
/// bounds.
#[derive(Clone)]
pub struct AllocationTracker {
    size: usize,
    unused: Vec<ByteRange>,
}

impl AllocationTracker {
    /// Constructs a new `AllocationTracker` of the provided `size`.
    pub fn new(size: usize) -> Self {
        AllocationTracker {
            size,
            unused: vec![ByteRange(0, size)],
        }
    }

    /// Returns the total memory size being tracked.
    pub fn len(&self) -> usize {
        self.size
    }

    pub fn count_free(&self) -> usize {
        self.unused.iter().fold(0, |acc, it| acc + it.len())
    }

    /// Checks if there is no empty space left in the tracked region.
    pub fn is_empty(&self) -> bool {
        self.unused.is_empty()
    }

    /// Returns a [`ByteRange`] encompassing the entire tracked memory region.
    pub fn whole_range(&self) -> ByteRange {
        ByteRange(0, self.size)
    }

    /// Grows the available memory range represented by this structure to
    /// provided `new_size`.
    pub fn grow(&mut self, new_size: usize) {
        match self.unused.last() {
            Some(it) => {
                // check whether the last free region ends at the end of
                // tracked region
                if it.1 == self.size {
                    let last = self
                        .unused
                        .last_mut()
                        .expect("free byte ranges isn't empty");
                    last.1 = new_size;
                } else {
                    self.unused.push(ByteRange(self.size, new_size));
                }
            }
            None => {
                self.unused.push(ByteRange(self.size, new_size));
            }
        }
        self.size = new_size;
    }

    /// Tries shrinking the available memory range represented by this structure
    /// to provided `new_size`, or returns
    /// [`AllocationTrackerError::Unshrinkable`] error if the represented memory
    /// range cannot be shrunk enough to fit the desired size.
    pub fn shrink(&mut self, new_size: usize) -> Result<(), AllocationTrackerError> {
        let last = self
            .unused
            .last_mut()
            .ok_or(AllocationTrackerError::Unshrinkable {
                required_size: self.size,
            })?;

        let reduction = self.size - new_size;
        if last.len() < reduction {
            return Err(AllocationTrackerError::Unshrinkable {
                required_size: self.size - last.len(),
            });
        }
        last.1 -= reduction;
        self.size = new_size;
        Ok(())
    }

    pub fn min_len(&self) -> usize {
        match self.unused.last() {
            Some(it) if it.1 == self.size => self.size - it.len(),
            _ => self.size,
        }
    }

    /// Removes tailing area of tracked memory bounds if it is marked as free
    /// and returns the new (reduced) size.
    ///
    /// If the tailing area was marked as occupied `None` is returned instead.
    pub fn shrink_to_fit(&mut self) -> Option<usize> {
        match self.unused.last() {
            Some(it) if it.1 == self.size => {
                let last = self.unused.pop().expect("free byte ranges isn't empty");
                self.size -= last.len();
                Some(self.size)
            }
            _ => None,
        }
    }

    /// Returns the next free memory region that can accommodate the given type
    /// `layout`.
    ///
    /// If the `layout` cannot be safely stored within any free segments of the
    /// represented memory region, `None` is returned instead.
    pub fn peek_next(&self, layout: Layout) -> Option<ByteRange> {
        if layout.size() == 0 {
            return Some(ByteRange::new(0, 0));
        }
        if layout.size() > self.size {
            return None;
        }

        let available = self.unused.iter().find(|it| {
            it.len() >= layout.size() && it.aligned(layout.align()).len() >= layout.size()
        })?;

        let usable = available.aligned(layout.align()).cap_size(layout.size());

        Some(usable)
    }

    /// Returns either a start position of a free byte range at the end of the
    /// tracker, or total size if end is occupied.
    #[inline]
    pub(crate) fn last_offset(&self) -> usize {
        match self.unused.last() {
            Some(it) if it.1 == self.size => it.0,
            _ => self.size,
        }
    }

    /// Returns number of tailing free bytes in the tracker
    #[inline]
    pub(crate) fn tailing_free_bytes(&self) -> usize {
        match self.unused.last() {
            Some(it) if it.1 == self.size => it.len(),
            _ => 0,
        }
    }

    /// Tries marking the provided memory `region` as not free, returning one
    /// of the following errors if that's not possible:
    ///
    /// - [`AllocationTrackerError::NotContained`]: If the provided region falls
    ///   outside of the memory tracked by the `AllocationTracker`.
    /// - [`AllocationTrackerError::AlreadyUsed`]: If the provided region isn't
    ///   free.
    pub fn take(&mut self, region: ByteRange) -> Result<(), AllocationTrackerError> {
        if region.len() == 0 {
            return Ok(());
        }
        if self.whole_range().contains(region) {
            std::panic::panic_any(AllocationTrackerError::NotContained);
        }

        let (i, found) = self
            .unused
            .iter()
            .enumerate()
            .find(|(_, it)| it.contains(region))
            .ok_or(AllocationTrackerError::AlreadyUsed)?;

        let (left, right) = found.difference_unchecked(region);

        if !left.is_empty() {
            self.unused[i] = left;
            if !right.is_empty() {
                self.unused.insert(i + 1, right);
            }
        } else if !right.is_empty() {
            self.unused[i] = right;
        } else {
            self.unused.remove(i);
        }

        Ok(())
    }

    /// Takes the next available memory region that can hold the provided
    /// `layout`.
    ///
    /// On success, it returns a [`ByteRange`] of the memory region that was
    /// taken, or a [`AllocationTrackerError::FullCapacity`] error if the
    /// requested `layout` cannot be placed within any free regions.
    pub fn take_next(
        &mut self,
        base_address: BaseAddress,
        layout: Layout,
    ) -> Result<ByteRange, AllocationTrackerError> {
        let base_address = match base_address {
            Some(it) => (it.as_ptr() as *mut u8) as usize,
            None => return Err(AllocationTrackerError::NoFreeMemory),
        };
        if layout.size() == 0 {
            return Ok(ByteRange::new(0, 0));
        } else if layout.size() > self.size {
            return Err(AllocationTrackerError::NoFreeMemory);
        }

        let (i, available) = self
            .unused
            .iter()
            .enumerate()
            .find(|(_, it)| {
                if it.len() < layout.size() {
                    return false;
                }

                let aligned = it
                    .offset(base_address)
                    .aligned(layout.align())
                    .cap_end(base_address + self.len());

                aligned.len() >= layout.size()
            })
            .ok_or(AllocationTrackerError::NoFreeMemory)?;

        let taken = available.aligned(layout.align()).cap_size(layout.size());

        let (left, right) = available.difference_unchecked(taken);

        if !left.is_empty() {
            self.unused[i] = left;
            if !right.is_empty() {
                self.unused.insert(i + 1, right);
            }
        } else if !right.is_empty() {
            self.unused[i] = right;
        } else {
            self.unused.remove(i);
        }

        Ok(taken)
    }

    /// Tries marking the provided memory `region` as free.
    ///
    /// # Errors
    ///
    /// In _release mode_ this function never fails.
    ///
    /// In _debug mode_ this function can return:
    /// - [`AllocationTrackerError::NotContained`] error if the provided region
    ///   falls outside of the memory tracked by the `AllocationTracker`.
    /// - [`AllocationTrackerError::DoubleFree`] error if the provided region is
    ///   
    pub fn release(&mut self, region: ByteRange) -> Result<(), AllocationTrackerError> {
        if region.len() == 0 {
            return Ok(());
        }
        #[cfg(debug_assertions)]
        if !self.whole_range().contains(region) {
            return Err(AllocationTrackerError::NotContained);
        }

        if let Some(found) = self
            .unused
            .iter_mut()
            .find(|it| region.1 == it.0 || it.1 == region.0 || it.contains(region))
        {
            #[cfg(debug_assertions)]
            if found.overlaps(region) {
                return Err(AllocationTrackerError::DoubleFree);
            }
            found.apply_union_unchecked(region);
        } else if let Some((i, _)) = self.unused.iter().enumerate().find(|it| it.0 > region.0) {
            self.unused.insert(i, region);
        } else {
            self.unused.push(region);
        }

        Ok(())
    }

    #[inline]
    pub(crate) fn clear(&mut self) {
        self.unused.clear();
        self.unused.push(self.whole_range())
    }
}

#[cfg(feature = "debug")]
impl core::fmt::Debug for AllocationTracker {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AllocationTracker")
            .field("size", &self.size)
            .field("unused", &self.unused)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use crate::raw::null_base;

    use super::*;

    fn mock_base(align: usize) -> BaseAddress {
        unsafe { Some(null_base(align)) }
    }

    #[test]
    fn new_allocation_tracker() {
        let tracker = AllocationTracker::new(1024);
        assert_eq!(tracker.len(), 1024);
        assert_eq!(tracker.is_empty(), false);
        assert_eq!(tracker.whole_range(), ByteRange(0, 1024));
    }

    #[test]
    fn take_and_release_allocation_tracker() {
        let mut tracker = AllocationTracker::new(1024);

        let range = tracker
            .take_next(mock_base(8), Layout::from_size_align(32, 8).unwrap())
            .unwrap();
        assert_eq!(range, ByteRange(0, 32));

        tracker
            .release(range)
            .expect("expected AllocationTracker to have the provided range marked as taken");
        assert_eq!(tracker.is_empty(), false);
    }

    #[test]
    fn peek_next_allocation_tracker() {
        let tracker = AllocationTracker::new(1024);

        let layout = Layout::from_size_align(64, 8).unwrap();
        let range = tracker.peek_next(layout).unwrap();
        assert_eq!(range, ByteRange(0, 64));
    }

    #[test]
    fn take_next_allocation_tracker() {
        let mut tracker = AllocationTracker::new(1024);

        let layout = Layout::from_size_align(128, 8).unwrap();
        let range = tracker.take_next(mock_base(8), layout).unwrap();
        assert_eq!(range, ByteRange(0, 128));
    }
}
