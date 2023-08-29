//! Module housing [`AllocationTracker`].

use core::alloc::Layout;

#[cfg(any(feature = "no_std"))]
use crate::types::*;
use crate::{error::ContiguousMemoryError, range::ByteRange};

/// A structure that keeps track of unused regions of memory within provided
/// bounds.
#[derive(Clone)]
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct AllocationTracker {
    size: usize,
    unused: Vec<ByteRange>,
}
impl AllocationTracker {
    /// Constructs a new `AllocationTracker` of the provided `size`.
    ///
    /// # Arguments
    ///
    /// * `size` - The total size of the memory region that will be tracked.
    pub fn new(size: usize) -> Self {
        let mut initial = Vec::new();
        initial.push(ByteRange(0, size));
        AllocationTracker {
            size,
            unused: initial,
        }
    }

    /// Returns the total memory size being tracked.
    pub fn len(&self) -> usize {
        self.size
    }

    /// Checks if there is no empty space left in the tracked region.
    pub fn is_empty(&self) -> bool {
        self.unused.is_empty()
    }

    /// Returns a [`ByteRange`] encompassing the entire tracked memory region.
    pub fn whole_range(&self) -> ByteRange {
        ByteRange(0, self.size)
    }

    /// Tries resizing the available memory range represented by this structure
    /// to the provided `new_size`.
    ///
    /// # Arguments
    ///
    /// * `new_size` - The desired new size of the memory region.
    ///
    /// # Returns
    ///
    /// A `Result` indicating success or a `ContiguousMemoryError` if an error
    /// occurs.
    ///
    /// # Errors
    ///
    /// This function can return the following errors:
    ///
    /// - [`ContiguousMemoryError::Unshrinkable`]: If the remaining free regions
    ///   cannot be shrunk to the desired size.
    pub fn resize(&mut self, new_size: usize) -> Result<(), ContiguousMemoryError> {
        if new_size == self.size {
            return Ok(());
        } else if new_size < self.size {
            let last = self
                .unused
                .last_mut()
                .ok_or(ContiguousMemoryError::Unshrinkable {
                    required_size: self.size,
                })?;

            let reduction = self.size - new_size;
            if last.len() < reduction {
                return Err(ContiguousMemoryError::Unshrinkable {
                    required_size: self.size - last.len(),
                });
            }
            last.1 -= reduction;
            self.size = new_size;
        } else {
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
        Ok(())
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
    /// [`Layout`].
    ///
    /// If the `layout` cannot be safely stored within any free segments of the
    /// represented memory region, `None` is returned.
    ///
    /// # Arguments
    ///
    /// * `layout` - The layout of the data to be stored.
    ///
    /// # Returns
    ///
    /// An optional [`ByteRange`] representing the next available memory region,
    /// or `None` if no suitable region is found.
    pub fn peek_next(&self, layout: Layout) -> Option<ByteRange> {
        if layout.size() > self.size {
            return None;
        }

        let available = self.unused.iter().find(|it| {
            it.len() >= layout.size() && it.aligned(layout.align()).len() >= layout.size()
        })?;

        let usable = available.aligned(layout.align()).cap_size(layout.size())?;

        Some(usable)
    }

    /// Tries marking the provided memory region as not free.
    ///
    /// # Arguments
    ///
    /// * `region` - The memory region to mark as not free.
    ///
    /// # Returns
    ///
    /// A `Result` indicating success or a `ContiguousMemoryError` if an error
    /// occurs.
    ///
    /// # Errors
    ///
    /// This function can return the following errors:
    ///
    /// - [`ContiguousMemoryError::NotContained`]: If the provided region falls
    ///   outside of the memory tracked by the `AllocationTracker`.
    /// - [`ContiguousMemoryError::AlreadyUsed`]: If the provided region isn't
    ///   free.
    pub fn take(&mut self, region: ByteRange) -> Result<(), ContiguousMemoryError> {
        if self.whole_range().contains(region) {
            return Err(ContiguousMemoryError::NotContained);
        }

        let (i, found) = self
            .unused
            .iter()
            .enumerate()
            .find(|(_, it)| it.contains(region))
            .ok_or(ContiguousMemoryError::AlreadyUsed)?;

        let (left, right) = found.difference_unchecked(region);

        if left.len() > 0 {
            self.unused[i] = left;
            if right.len() > 0 {
                self.unused.insert(i + 1, right);
            }
        } else if right.len() > 0 {
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
    /// taken.
    ///
    /// # Arguments
    ///
    /// * `layout` - The layout of the data to be stored.
    ///
    /// # Returns
    ///
    /// A `Result` indicating success with the allocated [`ByteRange`] or a
    /// `ContiguousMemoryError` if an error occurs.
    ///
    /// # Errors
    ///
    /// This function can return the following errors:
    ///
    /// - [`ContiguousMemoryError::NoStorageLeft`]: If the requested [`Layout`]
    ///   cannot be fitted within any free memory regions.
    pub fn take_next(&mut self, layout: Layout) -> Result<ByteRange, ContiguousMemoryError> {
        if layout.size() > self.size {
            return Err(ContiguousMemoryError::NoStorageLeft);
        }

        let (i, available) = self
            .unused
            .iter()
            .enumerate()
            .find(|(_, it)| {
                it.len() >= layout.size() && it.aligned(layout.align()).len() >= layout.size()
            })
            .ok_or(ContiguousMemoryError::NoStorageLeft)?;

        let taken = available
            .aligned(layout.align())
            .cap_size(layout.size())
            .ok_or(ContiguousMemoryError::NoStorageLeft)?;

        let (left, right) = available.difference_unchecked(taken);

        if left.len() > 0 {
            self.unused[i] = left;
            if right.len() > 0 {
                self.unused.insert(i + 1, right);
            }
        } else if right.len() > 0 {
            self.unused[i] = right;
        } else {
            self.unused.remove(i);
        }

        Ok(taken)
    }

    /// Tries marking the provided memory region as free.
    ///
    /// # Arguments
    ///
    /// * `region` - The memory region to mark as free.
    ///
    /// # Returns
    ///
    /// A `Result` indicating success or a `ContiguousMemoryError` if an error
    /// occurs.
    ///
    /// # Errors
    ///
    /// This function can return the following error:
    ///
    /// - [`ContiguousMemoryError::NotContained`]: If the provided region falls
    ///   outside of the memory tracked by the `AllocationTracker`.
    pub fn release(&mut self, region: ByteRange) -> Result<(), ContiguousMemoryError> {
        if !self.whole_range().contains(region) {
            return Err(ContiguousMemoryError::NotContained);
        }

        if let Some(found) = self
            .unused
            .iter_mut()
            .find(|it| region.1 == it.0 || it.1 == region.0 || it.contains(region))
        {
            if found.contains(region) {
                return Err(ContiguousMemoryError::DoubleFree);
            }
            found.merge_in_unchecked(region);
        } else {
            if let Some((i, _)) = self.unused.iter().enumerate().find(|it| it.0 > region.0) {
                self.unused.insert(i, region);
            } else {
                self.unused.push(region);
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_allocation_tracker() {
        let tracker = AllocationTracker::new(1024);
        assert_eq!(tracker.len(), 1024);
        assert_eq!(tracker.is_empty(), false);
        assert_eq!(tracker.whole_range(), ByteRange(0, 1024));
    }

    #[test]
    fn test_resize_allocation_tracker() {
        let mut tracker = AllocationTracker::new(1024);

        tracker.resize(512).unwrap();
        assert_eq!(tracker.len(), 512);

        tracker.resize(2048).unwrap();
        assert_eq!(tracker.len(), 2048);
    }

    #[test]
    fn test_take_and_release_allocation_tracker() {
        let mut tracker = AllocationTracker::new(1024);

        let range = tracker
            .take_next(Layout::from_size_align(32, 8).unwrap())
            .unwrap();
        assert_eq!(range, ByteRange(0, 32));

        tracker
            .release(range)
            .expect("expected AllocationTracker to have the provided range marked as taken");
        assert_eq!(tracker.is_empty(), false);
    }

    #[test]
    fn test_peek_next_allocation_tracker() {
        let tracker = AllocationTracker::new(1024);

        let layout = Layout::from_size_align(64, 8).unwrap();
        let range = tracker.peek_next(layout).unwrap();
        assert_eq!(range, ByteRange(0, 64));
    }

    #[test]
    fn test_take_next_allocation_tracker() {
        let mut tracker = AllocationTracker::new(1024);

        let layout = Layout::from_size_align(128, 8).unwrap();
        let range = tracker.take_next(layout).unwrap();
        assert_eq!(range, ByteRange(0, 128));
    }
}
