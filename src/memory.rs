//! Structs and code for memory management.

use core::{cmp, fmt::Write};
use core::{alloc::Layout, ptr::NonNull};

pub use crate::raw::{BaseAddress, BasePtr, MemoryBase};
use crate::types::HasLayout;

#[cfg(not(feature = "std"))]
use crate::types::{vec, Vec};
use crate::{range::ByteRange, MemoryError};

#[cfg(nightly)]
use core::alloc::Allocator;
#[cfg(not(nightly))]
use allocator_api2::alloc::Allocator;

#[cfg(nightly)]
pub use std::alloc::System;
#[cfg(not(nightly))]
pub use allocator_api2::alloc::System;

/// A structure that keeps track of unoccupied regions of memory.
///
/// This is used by [`ContiguousMemory`] to manage positions of stored items
/// while preventing overlap of assigned regions and proper alignment of stored
/// data.
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
    /// Constructs a new empty `SegmentTracker` of the provided `size`.
    ///
    /// # Examples
    /// ```
    /// # use contiguous_mem::memory::SegmentTracker;
    /// # use contiguous_mem::range::ByteRange;
    /// let tracker = SegmentTracker::new(1024);
    ///
    /// assert!(!tracker.is_full());
    /// assert_eq!(tracker.size(), 1024);
    /// assert_eq!(tracker.whole_range(), ByteRange(0, 1024));
    /// ```
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
    ///
    /// # Examples
    /// ```
    /// # use contiguous_mem::memory::SegmentTracker;
    /// let mut tracker = SegmentTracker::new(1024);
    ///
    /// assert_eq!(tracker.size(), 1024);
    ///
    /// tracker.grow(2048);
    ///
    /// assert_eq!(tracker.size(), 2048);
    /// ```
    pub fn size(&self) -> usize {
        self.size
    }

    /// Returns the sum of unoccupied bytes of all unused memory segments.
    ///
    /// # Examples
    /// ```
    /// # use contiguous_mem::memory::SegmentTracker;
    /// # use contiguous_mem::range::ByteRange;
    /// # use core::alloc::Layout;
    /// let mut tracker = SegmentTracker::new(1024);
    ///
    /// assert_eq!(tracker.count_free(), 1024);
    ///
    /// let layout = Layout::from_size_align(512, 8).unwrap();
    /// let _ = tracker.take_next(4, layout).unwrap();
    ///
    /// // both preceding 8 bytes and subsequent 504 bytes are counted towards
    /// // the total:
    /// assert_eq!(tracker.count_free(), 512);
    /// ```
    pub fn count_free(&self) -> usize {
        self.unoccupied.iter().fold(0, |acc, it| acc + it.len())
    }

    /// Returns `true` if there is no empty space left in the tracked region.
    ///
    /// # Examples
    /// ```
    /// # use contiguous_mem::memory::SegmentTracker;
    /// # use contiguous_mem::range::ByteRange;
    /// # use core::alloc::Layout;
    /// let mut tracker = SegmentTracker::new(1024);
    ///
    /// let layout = Layout::from_size_align(512, 8).unwrap();
    /// let _ = tracker.take_next(4, layout).unwrap();
    ///
    /// assert!(!tracker.is_full());
    ///
    /// let layout = Layout::from_size_align(504, 8).unwrap();
    /// let _ = tracker.take_next(4, layout).unwrap();
    ///
    /// assert!(!tracker.is_full());
    ///
    /// let layout = Layout::from_size_align(8, 4).unwrap();
    /// let _ = tracker.take_next(4, layout).unwrap();
    ///
    /// assert!(tracker.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        self.unoccupied.is_empty()
    }

    /// Returns a [`ByteRange`] encompassing the entire tracked memory region.
    ///
    /// # Examples
    /// ```
    /// # use contiguous_mem::memory::SegmentTracker;
    /// # use contiguous_mem::range::ByteRange;
    /// # use core::alloc::Layout;
    /// let mut tracker = SegmentTracker::new(1024);
    ///
    /// assert_eq!(tracker.whole_range(), ByteRange(0, 1024));
    ///
    /// let layout = Layout::from_size_align(512, 8).unwrap();
    /// let _ = tracker.take_next(4, layout).unwrap();
    ///
    /// assert_eq!(tracker.whole_range(), ByteRange(0, 1024));
    /// ```
    pub fn whole_range(&self) -> ByteRange {
        ByteRange(0, self.size)
    }

    /// Grows the available memory range represented by this structure to
    /// provided `new_size` and returns the new size.
    pub fn grow(&mut self, new_size: usize) -> usize {
        if new_size <= self.size {
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
        if new_size >= self.size {
            return self.size;
        }
        
        let last = match self.unoccupied.last_mut() {
            Some(it) => it,
            None => return self.size,
        };

        let reduction = self.size - new_size;
        let reduction = cmp::min(reduction, last.len());
        last.1 -= reduction;
        if last.is_empty() {
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

    /// Returns `true` if the provided type `layout` can be stored within any
    /// unused segments of the represented memory region.
    pub fn can_store(&self, base: MemoryBase, layout: impl HasLayout) -> bool {
        let layout = layout.as_layout();
        if layout.size() == 0 {
            return true;
        } else if layout.size() > self.size {
            return false;
        }

        self.unoccupied.iter().any(|it| {
            it.offset(base.pos_or_align()) // absolute range
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
    /// valid until this tracker gets mutated from somewhere else. The returned
    /// value can also apply mutation on `self` via a call to
    /// [`Location::mark_occupied`].
    pub fn peek_next(&mut self, base_pos: usize, layout: impl HasLayout) -> Option<Location<'_>> {
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
                it.offset(base_pos) // absolute range
                    .aligned(layout.align()) // properly aligned
                    .len() // length of
                    >= layout.size()
            })
            .min_by_key(|(_, it)| it.len())?;

        let available = found_range.aligned(layout.align()).cap_size(layout.size());

        Some(Location::new(self, found_position, *found_range, available))
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
    ///
    /// # Examples
    ///
    /// ```
    /// # use contiguous_mem::range::ByteRange;
    /// # use contiguous_mem::memory::SegmentTracker;
    /// # use core::alloc::Layout;
    /// let mut tracker = SegmentTracker::new(1024);
    ///
    /// let layout = Layout::from_size_align(128, 8).unwrap();
    /// let range = tracker.take_next(8, layout).unwrap();
    ///
    /// assert_eq!(range, ByteRange(0, 128));
    /// ```
    #[inline]
    pub fn take_next(&mut self, base_pos: usize, layout: impl HasLayout) -> Option<ByteRange> {
        let mut location = self.peek_next(base_pos, layout)?;
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
    ///
    /// # Examples
    /// ```
    /// # use contiguous_mem::range::ByteRange;
    /// # use contiguous_mem::memory::SegmentTracker;
    /// # use core::alloc::Layout;
    /// let mut tracker = SegmentTracker::new(1024);
    ///
    /// let range = tracker
    ///     .take_next(8, Layout::from_size_align(32, 8).unwrap())
    ///     .unwrap();
    /// assert_eq!(range, ByteRange(0, 32));
    ///
    /// tracker.release(range);
    /// assert!(!tracker.is_full());
    /// ```
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

    /// Clears all regions marked as occupied.
    #[inline]
    pub fn clear(&mut self) {
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

/// A result of [`SegmentTracker::peek_next`] which contains information about
/// available allocation slot and wherein a certain [`Layout`] could be placed.
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
            whole: ByteRange::EMPTY,
            usable: ByteRange::EMPTY,
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

    /// Returns `true` if the pointed-to location is zero-sized.
    #[inline]
    pub fn is_zero_sized(&self) -> bool {
        self.usable.is_empty()
    }

    /// Marks the pointed-to location as occupied.
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
/// Default implementation that uses a system allocator (`malloc`) is
/// [`alloc::System`](System). Other allocators are supported as well.
pub trait ManageMemory {
    /// Allocates a block of memory with size and alignment specified by
    /// `layout` argument.
    fn allocate(&self, layout: Layout) -> Result<BaseAddress, MemoryError>;

    /// Deallocates a block of memory of provided `base`.
    ///
    /// # Safety
    ///
    /// See: [alloc::Allocator::deallocate]
    unsafe fn deallocate(&self, base: MemoryBase);

    /// Shrinks the provided memory slice to `new_size`.
    ///
    /// Generally doesn't cause a move, but an implementation can choose to do
    /// so.
    ///
    /// # Safety
    ///
    /// See: [alloc::Allocator::shrink]
    unsafe fn shrink(&self, base: MemoryBase, new_size: usize) -> Result<BaseAddress, MemoryError>;

    /// Grows the provided memory slice to `new_size`.
    ///
    /// # Safety
    ///
    /// See: [alloc::Allocator::grow]
    unsafe fn grow(&self, base: MemoryBase, new_size: usize) -> Result<BaseAddress, MemoryError>;
}

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

    unsafe fn deallocate(&self, base: MemoryBase) {
        if base.is_allocated() {
            unsafe {
                Allocator::deallocate(
                    self,
                    NonNull::new_unchecked(base.as_ptr_mut()),
                    base.layout(),
                )
            }
        }
    }

    unsafe fn shrink(&self, base: MemoryBase, new_size: usize) -> Result<BaseAddress, MemoryError> {
        match base.address {
            Some(it) => {
                if new_size > 0 {
                    let new_layout = Layout::from_size_align(new_size, base.alignment())?;
                    Allocator::shrink(
                        self,
                        NonNull::new_unchecked(it.as_ptr() as *mut u8),
                        base.layout(),
                        new_layout,
                    )
                    .map(Some)
                    .map_err(MemoryError::from)
                } else {
                    Allocator::deallocate(
                        self,
                        NonNull::new_unchecked(it.as_ptr() as *mut u8),
                        base.layout(),
                    );
                    Ok(None)
                }
            }
            None => Ok(None),
        }
    }

    unsafe fn grow(&self, base: MemoryBase, new_size: usize) -> Result<BaseAddress, MemoryError> {
        match base.address {
            Some(it) => {
                let new_layout = Layout::from_size_align(new_size, base.alignment())?;
                Allocator::grow(
                    self,
                    NonNull::new_unchecked(it.as_ptr() as *mut u8),
                    base.layout(),
                    new_layout,
                )
                .map(Some)
                .map_err(MemoryError::from)
            }
            None => {
                if new_size == 0 {
                    Ok(None)
                } else {
                    let new_layout = Layout::from_size_align(new_size, base.alignment())?;
                    Allocator::allocate(self, new_layout)
                        .map(Some)
                        .map_err(MemoryError::from)
                }
            }
        }
    }
}

/// Provides a very verbose [`Display`][core::fmt::Display] of
/// [`SegmentTracker`] with address information.
#[cfg(feature = "debug")]
pub struct DisplaySegments(pub(crate) usize, pub(crate) SegmentTracker);
#[cfg(feature = "debug")]
impl core::fmt::Display for DisplaySegments {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        writeln!(f, "v- start: 0x{:X}", self.0)?;
        let mut len = 2;
        f.write_char('|')?;
        let mut location = self.0;
        for &u in &self.1.unoccupied {
            if u.0 != location - self.0 {
                let occupied = u.0 + self.0 - location;
                let used = format!("#..{}B..#", occupied);
                if used.len() < occupied {
                    f.write_str(&used)?;
                    len += used.len();
                } else {
                    f.write_str(&"#".repeat(occupied))?;
                    len += occupied;
                }
            }
            let space = (u.1.saturating_sub(u.0)).max(1);
            let start = format!("[0x{:X}", u.0 + self.0);
            let end = format!("0x{:X}]", u.1 + self.0);
            let total = format!("|{}B|", space);
            if start.len() + total.len() + end.len() >= space {
                write!(f, "{}{}{}", start, total, end)?;
                len += start.len() + total.len() + end.len();
            } else {
                write!(f, "{}|{}", start, end)?;
                len += start.len() + 1 + end.len();
            }
            location = self.0 + u.1;
        }
        if location != self.0 + self.1.size {
            let occupied = self.0 + self.1.size - location;
            let used = format!("#..{}B..#", occupied);
            if used.len() < occupied {
                f.write_str(&used)?;
                len += used.len();
            } else {
                f.write_str(&"#".repeat(occupied))?;
                len += occupied;
            }
        }
        f.write_char('|')?;
        writeln!(f, " total: {}B", self.1.size)?;
        let end = format!("end: 0x{:X} -^", self.0 + self.1.size);
        if end.len() > len {
            let end = format!("^- end: 0x{:X}", self.0 + self.1.size);
            write!(f, "{}{}", " ".repeat(len - 1), end)?;
        } else {
            write!(f, "{}{}", " ".repeat(len - end.len()), end)?;
        }
        
        Ok(())
    }
}
