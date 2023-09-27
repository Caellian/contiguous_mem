//! Structs and code for memory management.

use core::cmp;
use core::{alloc::Layout, ptr::NonNull};

use crate::common::HasLayout;
pub use crate::raw::{BaseAddress, BasePtr};

#[cfg(feature = "no_std")]
use crate::types::{vec, Vec};
use crate::{range::ByteRange, raw::base_addr_position, MemoryError};

#[cfg(feature = "no_std")]
pub use alloc::alloc;
#[cfg(not(feature = "no_std"))]
use std::alloc;

#[cfg(feature = "allocator_api")]
use alloc::Allocator;

/// A structure that keeps track of unoccupied regions of memory.
///
/// This is used by [`ContiguousMemory`] to manage
/// positions of stored items while preventing overlap of assigned regions and
/// proper alignment of stored data.
///
/// # Placement strategy
///
/// A region provided for a given [`Layout`] is the beginning of the smallest
/// unoccupied segment with appropriate leading padding required to keep the
/// value represented by the `Layout` valid.
///
/// Using the smallest unoccupied segment is necessary to reduce segmentation
/// that would occur if a greedier strategy (first available) were used.
///
/// A different approach may be taken in the future and this change isn't
/// considered breaking - [`ContiguousMemory`] provides no means of directly
/// accessing the raw bytes of the stored data (i.e. `as_bytes`) and placement
/// order, positions or even alignment of stored data shouldn't be relied upon.
///
/// [`Layout`]: core::alloc::Layout
/// [`ContiguousMemory`]: crate::ContiguousMemory
#[derive(Clone)]
pub struct SegmentTracker {
    size: usize,
    unoccupied: Vec<ByteRange>,
}

impl SegmentTracker {
    /// Constructs a new `SegmentTracker` of the provided `size`.
    pub fn new(size: usize) -> Self {
        SegmentTracker {
            size,
            unoccupied: if size > 0 {
                vec![ByteRange(0, size)]
            } else {
                vec![]
            },
        }
    }

    /// Returns the total memory size being tracked.
    pub fn size(&self) -> usize {
        self.size
    }

    /// Returns the sum of unoccupied bytes of all unused memory segments.
    pub fn count_free(&self) -> usize {
        self.unoccupied.iter().fold(0, |acc, it| acc + it.len())
    }

    /// Returns `true` if there is no empty space left in the tracked region.
    pub fn is_full(&self) -> bool {
        self.unoccupied.is_empty()
    }

    /// Returns a [`ByteRange`] encompassing the entire tracked memory region.
    pub fn whole_range(&self) -> ByteRange {
        ByteRange(0, self.size)
    }

    /// Grows the available memory range represented by this structure to
    /// provided `new_size` and returns the new size.
    pub fn grow(&mut self, new_size: usize) -> usize {
        if new_size < self.size {
            return self.size;
        }

        match self.unoccupied.last_mut() {
            Some(it) if it.1 == self.size => {
                // if the last free region ends at the end of tracked region
                // grow it
                it.1 = new_size;
            }
            _ => {
                self.unoccupied.push(ByteRange(self.size, new_size));
            }
        }
        self.size = new_size;
        self.size
    }

    /// Tries shrinking the available memory range represented by this structure
    /// to provided `new_size` and returns the new size.
    pub fn shrink(&mut self, new_size: usize) -> usize {
        let last = match self.unoccupied.last_mut() {
            Some(it) => it,
            None => return self.size,
        };

        let reduction = self.size - new_size;
        let reduction = cmp::min(reduction, last.len());
        last.1 -= reduction;
        if last.len() == 0 {
            self.unoccupied.pop();
        }
        self.size -= reduction;
        self.size
    }

    /// Removes tailing area of tracked memory bounds if it is marked as free
    /// and returns the new (reduced) size.
    ///
    /// If the tailing area was marked as occupied `None` is returned instead.
    pub fn shrink_to_fit(&mut self) -> Option<usize> {
        if self.unoccupied.last().map(|it| it.1) != Some(self.size) {
            return None;
        }

        let last = unsafe {
            // SAFETY: Prev. if returned if pop is None
            self.unoccupied.pop().unwrap_unchecked()
        };
        self.size -= last.len();

        Some(self.size)
    }

    /// Returns `true` if the provided type `layout` can ne stored within any
    /// unused segments of the represented memory region.
    pub fn can_store(&self, base_address: BaseAddress, layout: impl HasLayout) -> bool {
        let layout = layout.as_layout();
        if layout.size() == 0 {
            return true;
        } else if layout.size() > self.size {
            return false;
        }

        self.unoccupied.iter().enumerate().any(|(_, it)| {
            it.offset(base_addr_position(base_address)) // absolute range
                .aligned(layout.align()) // aligned to value
                .len()
                >= layout.size()
        })
    }

    /// Returns the appropriate [`Location`] that can accommodate the given type
    /// `layout`.
    ///
    /// If the `layout` cannot be stored within any unused segments of the
    /// represented memory region, `None` is returned instead.
    ///
    /// This function mutably borrows because the returned `Location` is only
    /// valid until this tracker gets mutated from somewhere else.
    /// The returned value can also apply mutation on `self` via a call to
    /// [`Location::mark_occupied`].
    pub fn peek_next(
        &mut self,
        base_address: BaseAddress,
        layout: impl HasLayout,
    ) -> Option<Location<'_>> {
        let layout = layout.as_layout();
        if layout.size() == 0 {
            return Some(Location::zero_sized(self));
        } else if layout.size() > self.size {
            return None;
        }

        // try to find the smallest free ByteRange that can hold the given
        // layout while keeping it properly aligned.
        let (found_position, found_range) = self
            .unoccupied
            .iter()
            .enumerate()
            .filter(|(_, it)| {
                it.offset(base_addr_position(base_address)) // absolute range
                    .aligned(layout.align()) // properly aligned
                    .len() // length of
                    >= layout.size()
            })
            .min_by_key(|(_, it)| it.len())?;

        let available = found_range.aligned(layout.align()).cap_size(layout.size());

        Some(Location::new(
            self,
            found_position,
            found_range.clone(),
            available,
        ))
    }

    /// Returns either a start position of a free byte range at the end of the
    /// tracker, or total size if end is occupied.
    #[inline]
    pub fn last_offset(&self) -> usize {
        match self.unoccupied.last() {
            Some(it) if it.1 == self.size => it.0,
            _ => self.size,
        }
    }

    /// Returns a copy largest free [`ByteRange`] tracked by this tracker.
    pub fn largest_free_range(&self) -> Option<ByteRange> {
        self.unoccupied.iter().max_by_key(|it| it.len()).copied()
    }

    /// Returns a number of tailing free bytes in the tracker.
    #[inline]
    pub fn tailing_free_bytes(&self) -> usize {
        match self.unoccupied.last() {
            Some(it) if it.1 == self.size => it.len(),
            _ => 0,
        }
    }

    /// Takes the next available memory region that can hold the provided
    /// `layout`.
    ///
    /// It returns a [`ByteRange`] of the memory region that was marked as used
    /// if successful, otherwise `None`
    #[inline]
    pub fn take_next(
        &mut self,
        base_address: BaseAddress,
        layout: impl HasLayout,
    ) -> Option<ByteRange> {
        let mut location = self.peek_next(base_address, layout)?;
        location.mark_occupied();
        Some(location.usable)
    }

    /// Tries marking the provided memory `region` as free.
    ///
    /// # Panics
    ///
    /// This function panics in debug mode if:
    /// * the provided region falls outside of the memory tracked by the
    ///   `SegmentTracker`, or
    /// * the provided region is in part or whole already marked as free.
    pub fn release(&mut self, region: ByteRange) {
        if region.is_empty() {
            return;
        }
        #[cfg(debug_assertions)]
        if !self.whole_range().contains(region) {
            panic!("{} not contained in segment tracker", region);
        }

        if let Some(found) = self
            .unoccupied
            .iter_mut()
            .find(|it| region.1 == it.0 || it.1 == region.0 || it.contains(region))
        {
            #[cfg(debug_assertions)]
            if found.overlaps(region) {
                panic!("double free in segment tracker");
            }
            found.apply_union_unchecked(region);
        } else if let Some((i, _)) = self
            .unoccupied
            .iter()
            .enumerate()
            .find(|it| it.0 > region.0)
        {
            self.unoccupied.insert(i, region);
        } else {
            self.unoccupied.push(region);
        }
    }

    #[inline]
    pub(crate) fn clear(&mut self) {
        self.unoccupied.clear();
        self.unoccupied.push(self.whole_range())
    }
}

#[cfg(feature = "debug")]
impl core::fmt::Debug for SegmentTracker {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SegmentTracker")
            .field("size", &self.size)
            .field("unused", &self.unoccupied)
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
        let tracker = SegmentTracker::new(1024);
        assert_eq!(tracker.size(), 1024);
        assert_eq!(tracker.is_full(), false);
        assert_eq!(tracker.whole_range(), ByteRange(0, 1024));
    }

    #[test]
    fn take_and_release_allocation_tracker() {
        let mut tracker = SegmentTracker::new(1024);

        let range = tracker
            .take_next(mock_base(8), Layout::from_size_align(32, 8).unwrap())
            .unwrap();
        assert_eq!(range, ByteRange(0, 32));

        tracker.release(range);
        assert_eq!(tracker.is_full(), false);
    }

    #[test]
    fn take_next_allocation_tracker() {
        let mut tracker = SegmentTracker::new(1024);

        let layout = Layout::from_size_align(128, 8).unwrap();
        let range = tracker.take_next(mock_base(8), layout).unwrap();
        assert_eq!(range, ByteRange(0, 128));
    }
}

/// A result of [`SegmentTracker::peek_next`] which contains information
/// about available allocation slot and wherein a certain [`Layout`] could be
/// placed.
///
/// `'a` is the lifetime of the [`SegmentTracker`] that produced this struct.
/// The reference is stored because it prevents any mutations from ocurring on
/// the tracker while a `Location` object is alive, which ensures it points to a
/// valid [`ByteRange`] stored in the tracker which can be acted upon without
/// incurring any additional lookup costs.
pub struct Location<'a> {
    parent: &'a mut SegmentTracker,
    index: usize,
    whole: ByteRange,
    usable: ByteRange,
}

impl<'a> Location<'a> {
    /// Creates a `Location` for a zero-sized struct in the `parent`.
    pub fn zero_sized(parent: &'a mut SegmentTracker) -> Self {
        Location {
            parent,
            index: 0,
            whole: ByteRange(0, 0),
            usable: ByteRange(0, 0),
        }
    }

    /// Creates a `Location` for a given `SegmentTracker` with required fields.
    pub fn new(
        parent: &'a mut SegmentTracker,
        index: usize,
        whole: ByteRange,
        usable: ByteRange,
    ) -> Self {
        Location {
            parent,
            index,
            whole,
            usable,
        }
    }

    /// Returns the index of the containing byte range for the insertion
    /// location.
    pub fn position(&self) -> usize {
        self.index
    }

    /// Returns the containing byte range of the insertion location.
    pub fn range(&self) -> ByteRange {
        self.whole
    }

    /// Returns a usable byte range of the insertion location.
    pub fn usable_range(&self) -> ByteRange {
        self.usable
    }

    /// Returns `true` if the pointed to location is zero-sized.
    #[inline]
    pub fn is_zero_sized(&self) -> bool {
        self.usable.len() == 0
    }

    /// Marks the pointed to location as occupied.
    pub fn mark_occupied(&mut self) {
        if self.is_zero_sized() {
            return;
        }

        let left = ByteRange(self.whole.0, self.usable.0);
        let right = ByteRange(self.usable.1, self.whole.1);

        // these are intentionally ordered by likelyhood to reduce cache misses
        match (left.is_empty(), right.is_empty()) {
            (true, false) => {
                // left aligned
                self.parent.unoccupied[self.index] = right;
            }
            (false, false) => {
                // remaining space before and after
                self.parent.unoccupied[self.index] = left;
                self.parent.unoccupied.insert(self.index + 1, right);
            }
            (true, true) => {
                // available occupies entirety of found
                self.parent.unoccupied.remove(self.index);
            }
            (false, true) => {
                // right aligned
                self.parent.unoccupied[self.index] = left;
            }
        }
    }
}

/// Memory manager controls allocation and deallocation of underlying memory
/// used by the container.
///
/// It also manages shrinking/growing of the container.
///
/// [`Layout`] arguments can have the size 0 and that _shouldn't_ cause a panic,
/// implementations of the trait must ensure to return `None` as [`BaseAddress`]
/// appropriately in those cases.
///
/// Default implementation is [`DefaultMemoryManager`].
///
/// If `allocator_api` feature is enabled, this trait is implemented for all
/// [allocators](alloc::Allocator).
pub trait ManageMemory {
    /// Allocates a block of memory with size and alignment specified by
    /// `layout` argument.
    fn allocate(&self, layout: Layout) -> Result<BaseAddress, MemoryError>;

    /// Deallocates a block of memory of provided `layout` at the specified
    /// `address`.
    ///
    /// # Safety
    ///
    /// See: [alloc::Allocator::deallocate]
    unsafe fn deallocate(&self, address: BaseAddress, layout: Layout);

    /// Shrinks the container underlying memory from `old_layout` size to
    /// `new_layout`.
    ///
    /// Generally doesn't cause a move, but an implementation can choose to do
    /// so.
    ///
    /// # Safety
    ///
    /// See: [alloc::Allocator::shrink]
    unsafe fn shrink(
        &self,
        address: BaseAddress,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<BaseAddress, MemoryError>;

    /// Grows the container underlying memory from `old_layout` size to
    /// `new_layout`.
    ///
    /// # Safety
    ///
    /// See: [alloc::Allocator::grow]
    unsafe fn grow(
        &self,
        address: BaseAddress,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<BaseAddress, MemoryError>;
}

/// Default [memory manager](ManageMemory) that uses the methods exposed by
/// [`alloc`] module.
#[derive(Clone, Copy)]
pub struct DefaultMemoryManager;
impl ManageMemory for DefaultMemoryManager {
    fn allocate(&self, layout: Layout) -> Result<BaseAddress, MemoryError> {
        if layout.size() == 0 {
            Ok(None)
        } else {
            unsafe {
                Ok(Some(NonNull::from(core::slice::from_raw_parts(
                    alloc::alloc(layout),
                    layout.size(),
                ))))
            }
        }
    }

    unsafe fn deallocate(&self, address: BaseAddress, layout: Layout) {
        if let Some(it) = address {
            alloc::dealloc(it.as_ptr() as *mut u8, layout);
        }
    }

    unsafe fn shrink(
        &self,
        address: BaseAddress,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<BaseAddress, MemoryError> {
        match address {
            Some(it) => Ok(if new_layout.size() > 0 {
                Some(NonNull::from(core::slice::from_raw_parts(
                    alloc::realloc(it.as_ptr() as *mut u8, old_layout, new_layout.size()),
                    new_layout.size(),
                )))
            } else {
                alloc::dealloc(it.as_ptr() as *mut u8, old_layout);
                None
            }),
            None => Ok(None),
        }
    }

    unsafe fn grow(
        &self,
        address: BaseAddress,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<BaseAddress, MemoryError> {
        match address {
            Some(it) => Ok(Some(NonNull::from(core::slice::from_raw_parts(
                alloc::realloc(it.as_ptr() as *mut u8, old_layout, new_layout.size()),
                new_layout.size(),
            )))),
            None => Ok({
                if new_layout.size() == 0 {
                    None
                } else {
                    Some(NonNull::from(core::slice::from_raw_parts(
                        alloc::alloc(new_layout),
                        new_layout.size(),
                    )))
                }
            }),
        }
    }
}

#[cfg(feature = "allocator_api")]
impl<A: Allocator> ManageMemory for A {
    fn allocate(&self, layout: Layout) -> Result<BaseAddress, MemoryError> {
        if layout.size() == 0 {
            Ok(None)
        } else {
            Allocator::allocate(self, layout)
                .map(Some)
                .map_err(MemoryError::from)
        }
    }

    unsafe fn deallocate(&self, address: BaseAddress, layout: Layout) {
        if let Some(allocated) = address {
            Allocator::deallocate(
                self,
                NonNull::new_unchecked(allocated.as_ptr() as *mut u8),
                layout,
            )
        }
    }

    unsafe fn shrink(
        &self,
        address: BaseAddress,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<BaseAddress, MemoryError> {
        match address {
            Some(it) => {
                if new_layout.size() > 0 {
                    Allocator::shrink(
                        self,
                        NonNull::new_unchecked(it.as_ptr() as *mut u8),
                        old_layout,
                        new_layout,
                    )
                    .map(Some)
                    .map_err(MemoryError::from)
                } else {
                    Allocator::deallocate(
                        self,
                        NonNull::new_unchecked(it.as_ptr() as *mut u8),
                        old_layout,
                    );
                    Ok(None)
                }
            }
            None => Ok(None),
        }
    }

    unsafe fn grow(
        &self,
        address: BaseAddress,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<BaseAddress, MemoryError> {
        match address {
            Some(it) => Allocator::grow(
                self,
                NonNull::new_unchecked(it.as_ptr() as *mut u8),
                old_layout,
                new_layout,
            )
            .map(Some)
            .map_err(MemoryError::from),
            None => {
                if new_layout.size() == 0 {
                    Ok(None)
                } else {
                    Allocator::allocate(self, new_layout)
                        .map(Some)
                        .map_err(MemoryError::from)
                }
            }
        }
    }
}
