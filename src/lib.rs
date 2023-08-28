#![cfg_attr(feature = "no_std", no_std)]
#![cfg_attr(feature = "ptr_metadata", feature(ptr_metadata))]

#[cfg(feature = "no_std")]
extern crate alloc;

#[cfg(any(
    all(not(feature = "std"), not(feature = "no_std")),
    all(feature = "std", feature = "no_std")
))]
compile_error!(
    "contiguous_mem requires either 'std' or 'no_std' feature to be enabled, not both or neither"
);

pub mod error;

use core::{
    cell::{Cell, RefCell},
    mem::size_of,
    ptr::{null_mut, write_unaligned},
};

#[cfg(not(feature = "ptr_metadata"))]
use core::marker::PhantomData;

#[cfg(feature = "ptr_metadata")]
use core::ptr::Pointee;

#[cfg(feature = "std")]
mod std_imports {
    pub use std::alloc::{Layout, LayoutError};

    pub use std::rc::Rc;
    pub use std::sync::Arc;
    pub use std::sync::Mutex;
    pub use std::sync::MutexGuard;

    pub use std::alloc::alloc as allocate;
    pub use std::alloc::dealloc as deallocate;
    pub use std::alloc::realloc as reallocate;
}
#[cfg(feature = "std")]
use std_imports::*;

#[cfg(feature = "no_std")]
mod nostd_imports {
    pub use alloc::alloc::{Layout, LayoutError};
    pub use alloc::vec::Vec;

    pub use alloc::rc::Rc;
    pub use alloc::sync::Arc;
    pub use spin::Mutex;
    pub use spin::MutexGuard;

    pub use alloc::alloc::alloc as allocate;
    pub use alloc::alloc::dealloc as deallocate;
    pub use alloc::alloc::realloc as reallocate;
}
#[cfg(feature = "no_std")]
use nostd_imports::*;

use portable_atomic::AtomicUsize;

use error::{ContiguousMemoryError, PoisonedMutex};

/// Trait that adds a method which mimics std `Result::map_err` on a Lock in order to unify
/// no_std and std environments.
///
/// This is necessary as [spin::Mutex::lock] doesn't return a Result but a [MutexGuard]
/// directly.
trait LockOr<T> {
    fn lock_or<F, O: FnOnce() -> F>(&self, op: O) -> Result<MutexGuard<T>, F>;
}
#[cfg(feature = "std")]
impl<T> LockOr<T> for Mutex<T> {
    fn lock_or<F, O: FnOnce() -> F>(&self, op: O) -> Result<MutexGuard<T>, F> {
        self.lock().map_err(|_| op())
    }
}
#[cfg(feature = "no_std")]
impl<T> LockOr<T> for Mutex<T> {
    fn lock_or<F, O: FnOnce() -> F>(&self, op: O) -> Result<MutexGuard<T>, F> {
        Ok(self.lock())
    }
}

/// Represents a range of bytes in [`AllocationTracker`] and [`ContiguousMemory`].
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(feature = "debug", test), derive(Debug))]
pub struct ByteRange(
    /// **Inclusive** lower bound of this byte range.
    usize,
    /// **Exclusive** upper bound of this byte range.
    usize,
);
impl ByteRange {
    /// Constructs a new byte range, ensuring that `from` and `to` are ordered correctly.
    ///
    /// # Arguments
    ///
    /// * `from` - The inclusive lower bound of the byte range.
    /// * `to` - The exclusive upper bound of the byte range.
    pub fn new(from: usize, to: usize) -> Self {
        ByteRange(from.min(to), to.max(from))
    }

    /// Constructs a new byte range without checking `from` and `to` ordering.
    ///
    /// # Arguments
    ///
    /// * `from` - The inclusive lower bound of the byte range.
    /// * `to` - The exclusive upper bound of the byte range.
    pub fn new_unchecked(from: usize, to: usize) -> Self {
        ByteRange(from, to)
    }

    /// Aligns this byte range to the provided `alignment`.
    ///
    /// # Arguments
    ///
    /// * `alignment` - The alignment to which the byte range should be aligned.
    pub fn aligned(&self, alignment: usize) -> Self {
        let offset = (self.0 as *const u8).align_offset(alignment);
        ByteRange(self.0 + offset, self.1)
    }

    /// Caps the size of this byte range to the provided `size` and returns it.
    /// If the size of this byte range is lesser than the required size, `None` is returned instead.
    ///
    /// # Arguments
    ///
    /// * `size` - The size to cap the byte range to.
    pub fn cap_size(&self, size: usize) -> Option<Self> {
        if self.len() < size {
            return None;
        }
        Some(ByteRange(self.0, self.0 + size))
    }

    /// Offsets this byte range by a provided unsigned offset.
    ///
    /// # Arguments
    ///
    /// * `offset` - The unsigned offset to add to both lower and upper bounds of the byte range.
    pub fn offset(&self, offset: usize) -> Self {
        ByteRange(self.0 + offset, self.1 + offset)
    }

    /// Offsets this byte range by a provided signed offset.
    ///
    /// # Arguments
    ///
    /// * `offset` - The signed offset to add to both lower and upper bounds of the byte range.
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
    ///
    /// # Arguments
    ///
    /// * `other` - The other byte range to check for containment.
    pub fn contains(&self, other: Self) -> bool {
        self.0 <= other.0 && other.1 <= self.1
    }

    /// Returns two byte ranges that remain when another `other` range is removed from this one.
    ///
    /// It is possible for either or both of the returned byte ranges to have a length of 0 if `other` is aligned with
    /// either the upper or lower bound of this range, or if it is equal to this range.
    ///
    /// # Arguments
    ///
    /// * `other` - The byte range to remove from this range.
    pub fn difference_unchecked(&self, other: Self) -> (Self, Self) {
        (ByteRange(self.0, other.0), ByteRange(other.1, self.1))
    }

    /// Merges this byte range with `other` and returns a byte range that contains both.
    ///
    /// # Arguments
    ///
    /// * `other` - The other byte range to merge with this one.
    pub fn merge_unchecked(&self, other: Self) -> Self {
        ByteRange(self.0.min(other.0), self.1.max(other.1))
    }

    /// Merges another `other` byte range into this one, resulting in a byte range that contains both.
    ///
    /// # Arguments
    ///
    /// * `other` - The other byte range to merge into this one.
    pub fn merge_in_unchecked(&mut self, other: Self) {
        self.0 = self.0.min(other.0);
        self.1 = self.1.max(other.1);
    }
}

/// A structure that keeps track of unused regions of memory within provided bounds.
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

    /// Tries resizing the available memory range represented by this structure to the
    /// provided `new_size`.
    ///
    /// # Arguments
    ///
    /// * `new_size` - The desired new size of the memory region.
    ///
    /// # Returns
    ///
    /// A `Result` indicating success or a `ContiguousMemoryError` if an error occurs.
    ///
    /// # Errors
    ///
    /// This function can return the following errors:
    ///
    /// - [`ContiguousMemoryError::Unshrinkable`]: If the remaining free regions cannot be shrunk to the desired size.
    pub fn resize(&mut self, new_size: usize) -> Result<(), ContiguousMemoryError> {
        if new_size == self.size {
            return Ok(());
        } else if new_size < self.size {
            let last = self
                .unused
                .last_mut()
                .ok_or(ContiguousMemoryError::Unshrinkable {
                    min_required: self.size,
                })?;

            let reduction = self.size - new_size;
            if last.len() < reduction {
                return Err(ContiguousMemoryError::Unshrinkable {
                    min_required: self.size - last.len(),
                });
            }
            last.1 -= reduction;
            self.size = new_size;
        } else {
            match self.unused.last() {
                Some(it) => {
                    // check whether the last free region ends at the end of tracked region
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

    /// Returns the next free memory region that can accommodate the given type [`Layout`].
    ///
    /// If the `layout` cannot be safely stored within any free segments of the represented memory region, `None` is returned.
    ///
    /// # Arguments
    ///
    /// * `layout` - The layout of the data to be stored.
    ///
    /// # Returns
    ///
    /// An optional [`ByteRange`] representing the next available memory region, or `None` if no suitable region is found.
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
    /// A `Result` indicating success or a `ContiguousMemoryError` if an error occurs.
    ///
    /// # Errors
    ///
    /// This function can return the following errors:
    ///
    /// - [`ContiguousMemoryError::NotContained`]: If the provided region falls outside of the memory tracked by the `AllocationTracker`.
    /// - [`ContiguousMemoryError::AlreadyUsed`]: If the provided region isn't free.
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

    /// Takes the next available memory region that can hold the provided `layout`.
    ///
    /// On success, it returns a [`ByteRange`] of the memory region that was taken.
    ///
    /// # Arguments
    ///
    /// * `layout` - The layout of the data to be stored.
    ///
    /// # Returns
    ///
    /// A `Result` indicating success with the allocated [`ByteRange`] or a `ContiguousMemoryError` if an error occurs.
    ///
    /// # Errors
    ///
    /// This function can return the following errors:
    ///
    /// - [`ContiguousMemoryError::NoStorageLeft`]: If the requested [`Layout`] cannot be fitted within any free memory regions.
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
    /// A `Result` indicating success or a `ContiguousMemoryError` if an error occurs.
    ///
    /// # Errors
    ///
    /// This function can return the following error:
    ///
    /// - [`ContiguousMemoryError::NotContained`]: If the provided region falls outside of the memory tracked by the `AllocationTracker`.
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

/// A trait defining the implementation details required by [`ContiguousMemory`].
pub trait ImplDetails {
    /// The type representing the base memory and allocation tracking.
    type Base: Clone;

    /// The type representing the allocation tracking mechanism.
    type AllocationTracker: Clone;

    /// The type representing the result of an allocation operation.
    type AllocResult<T: ?Sized>;

    /// The type representing the usage counter in [`crate::Ref`] type.
    type UseCounter: Clone;

    /// Indicates whether the container can grow when out of memory.
    const CAN_GROW: bool = true;

    /// Indicates whether locks are used for synchronization.
    const USE_LOCKS: bool = false;

    /// Creates a new instance of the base type from a raw pointer.
    fn new_base(value: *mut u8) -> Self::Base;

    /// Retrieves the base pointer from the base instance.
    fn get_base(base: &Self::Base) -> Result<*mut u8, ContiguousMemoryError>;

    /// Resizes and reallocates the base memory according to new capacity.
    fn reallocate(
        base: &mut Self::Base,
        layout: &mut Layout,
        new_capacity: usize,
    ) -> Result<*mut u8, ContiguousMemoryError>;

    /// Deallocates the base memory using layout information.
    fn deallocate(base: &Self::Base, layout: Layout);

    /// Creates a new allocation tracker for the specified capacity.
    fn new_allocation_tacker(capacity: usize) -> Self::AllocationTracker;

    /// Resizes the allocation tracker to the new capacity.
    fn resize_tracker(
        tracker: &mut Self::AllocationTracker,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError>;

    /// Finds the next free memory region for given layout in the tracker.
    fn next_free(
        tracker: &mut Self::AllocationTracker,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError>;

    /// Releases the specified memory range back to the allocation tracker.
    fn release_range(
        tracker: &mut Self::AllocationTracker,
        range: ByteRange,
    ) -> Result<(), ContiguousMemoryError>;

    /// Builds a reference for the stored data.
    fn build_ref<T>(
        base: &Self::Base,
        addr: *mut T,
        range: &ByteRange,
        tracker: &Self::AllocationTracker,
    ) -> Self::AllocResult<T>;

    /// Increments the usage counter for the reference.
    fn bump_ref(counter: &Self::UseCounter);

    /// Decrements the usage counter and returns `true` if it reaches zero.
    fn drop_ref(counter: &mut Self::UseCounter) -> bool;
}

/// A marker struct representing the behavior specialization for thread-safe operations within
/// [`ContiguousMemory`](crate::ContiguousMemory). This implementation ensures that the container's
/// operations can be used safely in asynchronous contexts, utilizing mutexes to prevent data races.
pub struct ThreadSafeImpl;
impl ImplDetails for ThreadSafeImpl {
    type Base = Arc<Mutex<*mut u8>>;
    type AllocationTracker = Arc<Mutex<AllocationTracker>>;
    type AllocResult<T: ?Sized> = CMRef<T, Self>;
    type UseCounter = Arc<AtomicUsize>;

    const USE_LOCKS: bool = true;

    #[inline(always)]
    fn new_base(value: *mut u8) -> Self::Base {
        Arc::new(Mutex::new(value))
    }

    #[inline(always)]
    fn get_base(base: &Self::Base) -> Result<*mut u8, ContiguousMemoryError> {
        base.lock_or(|| ContiguousMemoryError::Poisoned {
            which: PoisonedMutex::BaseAddress,
        })
        .map(|result| *result)
    }

    #[inline(always)]
    fn reallocate(
        base: &mut Self::Base,
        layout: &mut Layout,
        new_capacity: usize,
    ) -> Result<*mut u8, ContiguousMemoryError> {
        let mut lock = base.lock_or(|| ContiguousMemoryError::Poisoned {
            which: PoisonedMutex::BaseAddress,
        })?;
        *lock = unsafe { reallocate(*lock, *layout, new_capacity) };
        *layout = Layout::from_size_align(new_capacity, layout.align())?;
        Ok(*lock)
    }

    #[inline(always)]
    fn deallocate(base: &Self::Base, layout: Layout) {
        if let Ok(mut lock) = base.lock_or(|| ContiguousMemoryError::Poisoned {
            which: PoisonedMutex::BaseAddress,
        }) {
            unsafe { deallocate(*lock, layout) };
            *lock = null_mut();
        }
    }

    #[inline(always)]
    fn new_allocation_tacker(capacity: usize) -> Self::AllocationTracker {
        Arc::new(Mutex::new(AllocationTracker::new(capacity)))
    }

    #[inline(always)]
    fn resize_tracker(
        tracker: &mut Self::AllocationTracker,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        let mut lock = tracker.lock_or(|| ContiguousMemoryError::Poisoned {
            which: PoisonedMutex::AllocationTracker,
        })?;
        lock.resize(new_capacity)?;
        Ok(())
    }

    #[inline(always)]
    fn next_free(
        tracker: &mut Self::AllocationTracker,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError> {
        let mut lock = tracker.lock_or(|| ContiguousMemoryError::Poisoned {
            which: PoisonedMutex::AllocationTracker,
        })?;
        lock.take_next(layout)
    }

    #[inline(always)]
    fn release_range(
        tracker: &mut Self::AllocationTracker,
        range: ByteRange,
    ) -> Result<(), ContiguousMemoryError> {
        let mut lock = tracker.lock_or(|| ContiguousMemoryError::Poisoned {
            which: PoisonedMutex::AllocationTracker,
        })?;
        lock.release(range)
    }

    #[inline(always)]
    fn build_ref<T>(
        base: &Self::Base,
        _addr: *mut T,
        range: &ByteRange,
        tracker: &Self::AllocationTracker,
    ) -> Self::AllocResult<T> {
        CMRef {
            base: base.clone(),
            range: range.clone(),
            tracker: tracker.clone(),
            uses: Arc::new(AtomicUsize::new(1)),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }

    #[inline(always)]
    fn bump_ref(counter: &Self::UseCounter) {
        counter.add(1, portable_atomic::Ordering::Relaxed)
    }

    #[inline(always)]
    fn drop_ref(counter: &mut Self::UseCounter) -> bool {
        counter.sub(1, portable_atomic::Ordering::Relaxed);
        counter.load(portable_atomic::Ordering::Release) == 0
    }
}

/// A marker struct representing the behavior specialization for operations within
/// [`ContiguousMemory`](crate::ContiguousMemory) that do not require thread-safety.
/// This implementation skips mutexes, making it faster but unsuitable for concurrent usage.
pub struct NotThreadSafeImpl;
impl ImplDetails for NotThreadSafeImpl {
    type Base = Rc<Cell<*mut u8>>;
    type AllocationTracker = Rc<RefCell<AllocationTracker>>;
    type AllocResult<T: ?Sized> = CMRef<T, Self>;
    type UseCounter = Rc<Cell<usize>>;

    #[inline(always)]
    fn new_base(value: *mut u8) -> Self::Base {
        Rc::new(Cell::new(value))
    }

    #[inline(always)]
    fn get_base(base: &Self::Base) -> Result<*mut u8, ContiguousMemoryError> {
        Ok(base.get())
    }

    #[inline(always)]
    fn reallocate(
        base: &mut Self::Base,
        layout: &mut Layout,
        new_capacity: usize,
    ) -> Result<*mut u8, ContiguousMemoryError> {
        let value = unsafe { reallocate(base.get(), *layout, new_capacity) };
        base.set(value);
        *layout = Layout::from_size_align(new_capacity, layout.align())?;
        Ok(value)
    }

    #[inline(always)]
    fn deallocate(base: &Self::Base, layout: Layout) {
        unsafe { deallocate(base.get(), layout) };
        base.set(null_mut())
    }

    #[inline(always)]
    fn new_allocation_tacker(capacity: usize) -> Self::AllocationTracker {
        Rc::new(RefCell::new(AllocationTracker::new(capacity)))
    }

    #[inline(always)]
    fn resize_tracker(
        tracker: &mut Self::AllocationTracker,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        tracker.borrow_mut().resize(new_capacity)
    }

    #[inline(always)]
    fn next_free(
        tracker: &mut Self::AllocationTracker,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError> {
        tracker
            .try_borrow_mut()
            .map_err(|_| ContiguousMemoryError::TrackerInUse)?
            .take_next(layout)
    }

    #[inline(always)]
    fn release_range(
        tracker: &mut Self::AllocationTracker,
        range: ByteRange,
    ) -> Result<(), ContiguousMemoryError> {
        tracker
            .try_borrow_mut()
            .map_err(|_| ContiguousMemoryError::TrackerInUse)?
            .release(range)
    }

    #[inline(always)]
    fn build_ref<T>(
        base: &Self::Base,
        _addr: *mut T,
        range: &ByteRange,
        tracker: &Self::AllocationTracker,
    ) -> Self::AllocResult<T> {
        CMRef {
            base: base.clone(),
            range: range.clone(),
            tracker: tracker.clone(),
            uses: Rc::new(Cell::new(1)),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }

    #[inline(always)]
    fn bump_ref(counter: &Self::UseCounter) {
        counter.set(counter.get() + 1);
    }

    #[inline(always)]
    fn drop_ref(counter: &mut Self::UseCounter) -> bool {
        counter.set(counter.get() - 1);
        counter.get() == 0
    }
}

/// A marker struct representing the behavior specialization for a highly performance-optimized,
/// yet unsafe implementation within [`ContiguousMemory`](crate::ContiguousMemory). This trait is used when
/// the exact required size is known during construction, and when the container is guaranteed
/// to outlive any pointers to data contained in the memory block.
pub struct FixedSizeImpl;
impl ImplDetails for FixedSizeImpl {
    type Base = *mut u8;
    type AllocationTracker = AllocationTracker;
    type AllocResult<T: ?Sized> = *mut T;
    type UseCounter = ();

    const CAN_GROW: bool = false;

    #[inline(always)]
    fn new_base(value: *mut u8) -> Self::Base {
        value
    }

    #[inline(always)]
    fn get_base(base: &Self::Base) -> Result<*mut u8, ContiguousMemoryError> {
        Ok(*base)
    }

    #[inline(always)]
    fn reallocate(
        _base: &mut Self::Base,
        _layout: &mut Layout,
        _new_capacity: usize,
    ) -> Result<*mut u8, ContiguousMemoryError> {
        unimplemented!("can't reallocate ContiguousMemory with FixedSizeImpl");
    }

    #[inline(always)]
    fn deallocate(base: &Self::Base, layout: Layout) {
        unsafe {
            deallocate(*base, layout);
        }
    }

    #[inline(always)]
    fn new_allocation_tacker(capacity: usize) -> Self::AllocationTracker {
        AllocationTracker::new(capacity)
    }

    #[inline(always)]
    fn resize_tracker(
        _tracker: &mut Self::AllocationTracker,
        _new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        Err(ContiguousMemoryError::NoStorageLeft)
    }

    #[inline(always)]
    fn next_free(
        tracker: &mut Self::AllocationTracker,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError> {
        tracker.take_next(layout)
    }

    #[inline(always)]
    fn release_range(
        tracker: &mut Self::AllocationTracker,
        range: ByteRange,
    ) -> Result<(), ContiguousMemoryError> {
        tracker.release(range)
    }

    #[inline(always)]
    fn build_ref<T>(
        _base: &Self::Base,
        addr: *mut T,
        _range: &ByteRange,
        _tracker: &Self::AllocationTracker,
    ) -> Self::AllocResult<T> {
        addr
    }

    #[inline(always)]
    fn bump_ref(_counter: &Self::UseCounter) {
        unimplemented!("CMRef not implemented for FixedSizeImpl ContiguousMemory")
    }

    #[inline(always)]
    fn drop_ref(_counter: &mut Self::UseCounter) -> bool {
        unimplemented!("CMRef not implemented for FixedSizeImpl ContiguousMemory")
    }
}

/// A memory container for efficient allocation and storage of contiguous data.
///
/// This structure manages a contiguous block of memory, allowing for the storage of arbitrary data
/// while ensuring that stored items are placed adjacently without imposing any restrictions on layout,
/// such as those found in memory pools or the standard library's [Vec].
///
/// The `ContiguousMemory` type is particularly useful for scenarios where data locality and efficient
/// memory usage are crucial, as it provides a means to allocate and manage memory in a linear fashion.
///
/// # Performance
///
/// The [`store`] operation has a generally constant time complexity when storing items with the same layout,
/// as it primarily involves finding available memory regions. The time complexity increases linearly with the
/// number of gaps between previously stored items, making it an effective choice for maintaining data locality.
///
/// [`store`]: ContiguousMemory::store
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct ContiguousMemory<S: ImplDetails = NotThreadSafeImpl> {
    base: S::Base,
    layout: Layout,
    tracker: S::AllocationTracker,
}

impl<S: ImplDetails> ContiguousMemory<S> {
    /// Creates a new `ContiguousMemory` instance with the specified capacity and alignment.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The initial capacity of the memory container.
    /// * `alignment` - The alignment requirement for memory allocations.
    ///
    /// # Returns
    ///
    /// A `Result` containing the newly created `ContiguousMemory` instance on success,
    /// or a `LayoutError` if the memory layout cannot be satisfied.
    pub fn new(capacity: usize, alignment: usize) -> Result<Self, LayoutError> {
        let layout = Layout::from_size_align(capacity, alignment)?;
        let base = unsafe { allocate(layout) };
        Ok(ContiguousMemory {
            base: S::new_base(base),
            layout,
            tracker: S::new_allocation_tacker(capacity),
        })
    }

    /// Retrieves the base address of the allocated memory.
    ///
    /// # Safety
    ///
    /// This function is marked as unsafe because it returns a raw pointer to the allocated memory.
    ///
    /// # Returns
    ///
    /// A `Result` containing the base address of the allocated memory on success,
    /// or [`ContiguousMemoryError::Poisoned`] error when the Mutex holding the base address is poisoned.
    pub unsafe fn get_base(&self) -> Result<*mut u8, ContiguousMemoryError> {
        S::get_base(&self.base)
    }

    /// Returns the current capacity of the memory container.
    ///
    /// The capacity represents the size of the memory block that has been allocated
    /// for storing data. It may be larger than the amount of data currently stored
    /// within the container.
    pub fn get_capacity(&self) -> usize {
        self.layout.size()
    }

    /// Resizes the memory container to the specified capacity.
    ///
    /// This function can either grow or shrink the container based on the new capacity.
    ///
    /// # Arguments
    ///
    /// * `new_capacity` - The desired new capacity of the memory container.
    ///
    /// # Returns
    ///
    /// A `Result` indicating success on resizing the container, or a `ContiguousMemoryError` if an error occurs.
    ///
    /// # Errors
    ///
    /// This function can return the following errors:
    ///
    /// - [`ContiguousMemoryError::Poisoned`]: This error can occur if the mutex holding the base address or
    ///   the [`AllocationTracker`](crate::AllocationTracker) is poisoned. This error suggests potential thread contention issues.
    ///
    /// - [`ContiguousMemoryError::Unshrinkable`]: This error occurs when attempting to shrink the memory container, but
    ///   the stored data prevents the container from being shrunk to the desired capacity.
    pub fn resize(&mut self, new_capacity: usize) -> Result<(), ContiguousMemoryError> {
        if new_capacity == self.layout.size() {
            return Ok(());
        }

        let old_capacity = self.layout.size();
        S::resize_tracker(&mut self.tracker, new_capacity)?;
        match S::reallocate(&mut self.base, &mut self.layout, new_capacity) {
            Ok(_) => {}
            Err(ContiguousMemoryError::Poisoned { which }) if S::USE_LOCKS => {
                S::resize_tracker(&mut self.tracker, old_capacity)?;
                return Err(ContiguousMemoryError::Poisoned { which });
            }
            Err(other) => return Err(other),
        }

        Ok(())
    }

    /// Stores a value of type `T` in the memory container.
    ///
    /// This operation allocates memory for the provided value and stores it in the contiguous memory block.
    ///
    /// # Arguments
    ///
    /// * `value` - The value of type `T` to be stored in the memory container.
    ///
    /// # Returns
    ///
    /// A `Result` that encapsulates the result of the storage operation:
    ///
    /// - If the implementation details type `S` is [`NotThreadSafeImpl`](crate::NotThreadSafeImpl)
    ///   or [`ThreadSafeImpl`](crate::ThreadSafeImpl), the result will be a [`crate::Ref`] pointing to the stored value.
    ///   This reference provides a convenient and safe way to access and manipulate the stored data within the memory block.
    ///
    /// - If the implementation details type `S` is [`FixedSizeImpl`](crate::FixedSizeImpl), the result will be a raw pointer
    ///   (`*mut T`) to the stored value. This is due to the fact that fixed-size container won't move which means
    ///   the pointer will not be invalidated.
    ///
    /// The returned [`Result`] indicates success or an error if the storage operation encounters any issues.
    ///
    /// # Errors
    ///
    /// This function can return the following errors:
    ///
    /// - [`ContiguousMemoryError::NoStorageLeft`]: Only returned when the implementation details type `S`
    ///   is [`FixedSizeImpl`](crate::FixedSizeImpl) and indicates that the container couldn't accommodate the
    ///   provided data due to size limitations. Other implementation details grow the container instead.
    ///
    /// - [`ContiguousMemoryError::Poisoned`]: This error can occur when the [`AllocationTracker`](crate::AllocationTracker)
    ///   associated with the memory container is poisoned.
    ///
    pub fn store<T>(&mut self, value: T) -> Result<S::AllocResult<T>, ContiguousMemoryError> {
        let layout = Layout::new::<T>();

        let (addr, range) = loop {
            match S::next_free(&mut self.tracker, layout) {
                Ok(taken) => {
                    let found = (taken.0 + S::get_base(&self.base)? as usize) as *mut T;
                    unsafe {
                        write_unaligned(found, value);
                    }
                    break (found, taken);
                }
                Err(ContiguousMemoryError::NoStorageLeft) if S::CAN_GROW => {
                    self.resize(self.layout.size() * 2)?;
                }
                Err(other) => return Err(other),
            }
        };

        Ok(S::build_ref(&self.base, addr, &range, &self.tracker))
    }
}

impl ContiguousMemory<FixedSizeImpl> {
    #[inline(always)]
    pub unsafe fn free_typed<T>(&mut self, value: *mut T) -> Result<(), ContiguousMemoryError> {
        Self::free(self, value, size_of::<T>())
    }

    pub unsafe fn free<T>(
        &mut self,
        value: *mut T,
        size: usize,
    ) -> Result<(), ContiguousMemoryError> {
        FixedSizeImpl::release_range(
            &mut self.tracker,
            ByteRange(value as usize, value as usize + size),
        )
    }
}

/// A type alias for [`ContiguousMemory`](crate::ContiguousMemory) that enables references to data stored within it
/// to be used safely in asynchronous contexts. This version uses a thread-safe implementation.
pub type SyncContiguousMemory = ContiguousMemory<ThreadSafeImpl>;

/// A type alias for [`ContiguousMemory`](crate::ContiguousMemory) that offers a synchronous implementation without
/// using internal mutexes. This version is faster but doesn't provide thread safety. It allows the container to be
/// shrunk or grown to fit more data.
pub type GrowableContiguousMemory = ContiguousMemory<NotThreadSafeImpl>;

/// A type alias for [`ContiguousMemory`](crate::ContiguousMemory) that provides a highly performance-optimized
/// (unsafe) implementation. It's suitable when the exact required size is known during construction and when
/// the container is guaranteed to outlive any references pointing to it.
pub type FixedContiguousMemory = ContiguousMemory<FixedSizeImpl>;

impl<S: ImplDetails> Drop for ContiguousMemory<S> {
    fn drop(&mut self) {
        S::deallocate(&self.base, self.layout)
    }
}

/// A reference to `T` data stored in a [`ContiguousMemory`] structure.
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct CMRef<T: ?Sized, S: ImplDetails = NotThreadSafeImpl> {
    base: S::Base,
    range: ByteRange,
    tracker: S::AllocationTracker,
    uses: S::UseCounter,
    #[cfg(feature = "ptr_metadata")]
    metadata: <T as Pointee>::Metadata,
    #[cfg(not(feature = "ptr_metadata"))]
    _phantom: PhantomData<T>,
}
/// [`CMRef`] re-export to keep API compatibility with 0.1.*
pub type Ref<T, S = NotThreadSafeImpl> = CMRef<T, S>;

#[cfg(feature = "ptr_metadata")]
impl<T: Sized, S: ImplDetails> CMRef<T, S> {
    pub unsafe fn as_dyn<Dyn: ?Sized>(
        &self,
        metadata: <Dyn as Pointee>::Metadata,
    ) -> CMRef<Dyn, S> {
        CMRef {
            base: self.base.clone(),
            range: self.range.clone(),
            tracker: self.tracker.clone(),
            uses: self.uses.clone(),
            #[cfg(feature = "ptr_metadata")]
            metadata: core::mem::transmute(metadata),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }
}

#[cfg(not(feature = "ptr_metadata"))]
impl<T: Sized, S: ImplDetails> CMRef<T, S> {
    /// Tries accessing referenced data at its current location.
    ///
    /// Returns a [`Poisoned`](ContiguousMemoryError::Poisoned) error if the Mutex
    /// holding the `base` address pointer has been poisoned.
    pub fn get(&self) -> Result<&T, ContiguousMemoryError> {
        unsafe {
            let base = S::get_base(&self.base)?.offset(self.range.0 as isize);
            Ok(&*(base as *mut T))
        }
    }
}

#[cfg(feature = "ptr_metadata")]
impl<T: ?Sized, S: ImplDetails> CMRef<T, S> {
    /// Tries accessing referenced data at its current location.
    ///
    /// Returns a [`Poisoned`](ContiguousMemoryError::Poisoned) error if the Mutex
    /// holding the `base` address pointer has been poisoned.
    pub fn get(&self) -> Result<&T, ContiguousMemoryError> {
        unsafe {
            let base = S::get_base(&self.base)?.offset(self.range.0 as isize);
            let fat: *const T = core::ptr::from_raw_parts::<T>(base as *const (), self.metadata);
            Ok(&*fat)
        }
    }
}

impl<T, S: ImplDetails> Clone for CMRef<T, S> {
    fn clone(&self) -> Self {
        S::bump_ref(&self.uses);
        CMRef {
            base: self.base.clone(),
            range: self.range.clone(),
            tracker: self.tracker.clone(),
            uses: self.uses.clone(),
            #[cfg(feature = "ptr_metadata")]
            metadata: self.metadata.clone(),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }
}

impl<T: ?Sized, S: ImplDetails> Drop for CMRef<T, S> {
    fn drop(&mut self) {
        if S::drop_ref(&mut self.uses) {
            let _ = S::release_range(&mut self.tracker, self.range);
        }
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

    #[test]
    fn test_new_contiguous_memory() {
        let memory = ContiguousMemory::<NotThreadSafeImpl>::new(1024, 8).unwrap();
        assert_eq!(memory.get_capacity(), 1024);
    }

    #[test]
    fn test_store_and_get_contiguous_memory() {
        let mut memory = ContiguousMemory::<NotThreadSafeImpl>::new(1024, 8).unwrap();

        let value = 42u32;
        let stored_ref = memory.store(value).unwrap();
        let retrieved_value = stored_ref.get().unwrap();
        assert_eq!(*retrieved_value, value);
    }

    #[test]
    fn test_resize_contiguous_memory() {
        let mut memory = ContiguousMemory::<NotThreadSafeImpl>::new(1024, 8).unwrap();

        memory.resize(512).unwrap();
        assert_eq!(memory.get_capacity(), 512);

        memory.resize(2048).unwrap();
        assert_eq!(memory.get_capacity(), 2048);
    }

    #[test]
    fn test_growable_contiguous_memory() {
        let mut memory = GrowableContiguousMemory::new(1024, 8).unwrap();

        let value = 42u32;
        let stored_ref = memory.store(value).unwrap();
        let retrieved_value = stored_ref.get().unwrap();
        assert_eq!(*retrieved_value, value);

        memory.resize(2048).unwrap();
        assert_eq!(memory.get_capacity(), 2048);
    }

    #[test]
    fn test_fixed_contiguous_memory() {
        let mut memory = FixedContiguousMemory::new(1024, 8).unwrap();

        let value = 42u32;
        let stored_ref = memory.store(value).unwrap();
        unsafe {
            assert_eq!(*stored_ref, value);
        }

        // No resize allowed for FixedContiguousMemory
        assert!(memory.resize(2048).is_err());
    }

    struct TestStruct1 {
        field1: u32,
        field2: u64,
    }

    struct TestStruct2 {
        field1: u16,
        field2: f32,
        field3: i32,
    }

    #[test]
    fn test_store_structs_with_different_layouts() {
        let mut memory = ContiguousMemory::<NotThreadSafeImpl>::new(1024, 8).unwrap();

        let struct1 = TestStruct1 {
            field1: 42,
            field2: 1234567890,
        };
        let struct2 = TestStruct2 {
            field1: 123,
            field2: 3.14,
            field3: -42,
        };

        let stored_struct1 = memory.store(struct1).unwrap();
        let stored_struct2 = memory.store(struct2).unwrap();

        let retrieved_struct1 = stored_struct1.get().unwrap();
        assert_eq!(retrieved_struct1.field1, 42);
        assert_eq!(retrieved_struct1.field2, 1234567890);

        let retrieved_struct2 = stored_struct2.get().unwrap();
        assert_eq!(retrieved_struct2.field1, 123);
        assert_eq!(retrieved_struct2.field2, 3.14);
        assert_eq!(retrieved_struct2.field3, -42);
    }
}
