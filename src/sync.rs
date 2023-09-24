use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem::{align_of, size_of, ManuallyDrop};

use crate::error::{ContiguousMemoryError, LockTarget, LockingError};
use crate::range::ByteRange;
use crate::raw::*;
use crate::refs::{sealed::ReferenceState, SyncContiguousEntryRef};
use crate::types::*;
use crate::ImplConcurrent;

/// A collection that can store different data types in a contigous block of
/// memory.
///
/// Note that copying this structure creates a copy which represents the same
/// internal state.
/// If you need to copy the memory region into a new container use:
/// [`SyncContiguousMemory::copy_data`]
///
/// # Example
///
/// ```rust
#[doc = include_str!("../examples/sync_impl.rs")]
/// ```
#[derive(Clone)]
pub struct SyncContiguousMemory<A: MemoryManager = DefaultMemoryManager> {
    inner: Arc<MemoryState<ImplConcurrent, A>>,
}

impl SyncContiguousMemory {
    /// Creates a new zero-sized `SyncContiguousMemory` instance aligned with
    /// alignment of `usize`.
    pub fn new() -> Self {
        Self {
            inner: unsafe {
                MemoryState::new_sync(Layout::from_size_align_unchecked(0, align_of::<usize>()))
                    .expect("unable to create an empty container")
            },
        }
    }

    /// Creates a new `SyncContiguousMemory` instance with the specified
    /// `capacity`, aligned with alignment of `usize`.
    ///
    /// # Panics
    ///
    /// Panics if capacity exceeds `isize::MAX` bytes or the allocator can't
    /// provide required amount of memory.
    pub fn new_with_capacity(capacity: usize) -> Self {
        if !is_layout_valid(capacity, align_of::<usize>()) {
            panic!(
                "capacity too large; max: {}",
                isize::MAX as usize - (align_of::<usize>() - 1)
            )
        }
        Self::new_with_layout(unsafe {
            Layout::from_size_align_unchecked(capacity, core::mem::align_of::<usize>())
        })
    }

    /// Creates a new `SyncContiguousMemory` instance with capacity and
    /// alignment of the provided `layout`.
    ///
    /// # Panics
    ///
    /// Panics if capacity exceeds `isize::MAX` bytes or the allocator can't
    /// provide required amount of memory.
    pub fn new_with_layout(layout: Layout) -> Self {
        Self {
            inner: match MemoryState::new_sync(layout) {
                Ok(it) => it,
                Err(_) => unreachable!("unable to create a container with layout: {:?}", layout),
            },
        }
    }
}

impl<A: MemoryManager> SyncContiguousMemory<A> {
    /// Creates a new zero-sized `SyncContiguousMemory` instance aligned with
    /// alignment of `usize`.
    pub fn new_with_alloc(alloc: A) -> Self {
        unsafe {
            Self {
                inner: MemoryState::new_sync_with_alloc(
                    Layout::from_size_align_unchecked(0, align_of::<usize>()),
                    alloc,
                )
                .expect("unable to create an empty container"),
            }
        }
    }

    /// Creates a new `SyncContiguousMemory` instance with the specified `capacity`,
    /// aligned with alignment of `usize`.
    pub fn new_with_capacity_and_alloc(capacity: usize, alloc: A) -> Self {
        if !is_layout_valid(capacity, align_of::<usize>()) {
            panic!(
                "capacity too large; max: {}",
                isize::MAX as usize - (align_of::<usize>() - 1)
            )
        }
        unsafe {
            Self::new_with_layout_and_alloc(
                Layout::from_size_align_unchecked(capacity, align_of::<usize>()),
                alloc,
            )
        }
    }

    /// Creates a new `SyncContiguousMemory` instance with capacity and
    /// alignment of the provided `layout`.
    ///
    /// This method will panic if there's no more memory available.
    ///
    /// # Panics
    ///
    /// Panics if the allocator can't provide required amount of memory.
    pub fn new_with_layout_and_alloc(layout: Layout, alloc: A) -> Self {
        Self {
            inner: match MemoryState::new_sync_with_alloc(layout, alloc) {
                Ok(it) => it,
                Err(_) => unreachable!("unable to create a container with layout: {:?}", layout),
            },
        }
    }

    /// Returns the base address of the allocated memory or a
    /// [`LockingError::Poisoned`] error if the mutex holding the base address
    /// has been poisoned.
    ///
    /// This function will block the current thread until base address RwLock
    /// doesn't become readable.
    #[inline]
    pub fn get_base(&self) -> Result<BaseAddress, LockingError> {
        self.inner
            .base
            .read_named(LockTarget::BaseAddress)
            .map(|it| *it)
    }

    /// Returns the current capacity of the memory container.
    ///
    /// The capacity represents the size of the memory block that has been
    /// allocated for storing data. It may be larger than the amount of data
    /// currently stored within the container.
    #[inline]
    pub fn get_capacity(&self) -> usize {
        self.inner.capacity.load(Ordering::Acquire)
    }

    /// Returns the alignment of the memory container.
    #[inline]
    pub fn get_align(&self) -> usize {
        self.inner.alignment
    }

    /// Returns the layout of the memory region containing stored data.
    #[inline]
    pub fn get_layout(&self) -> Layout {
        unsafe {
            // SAFETY: Constructor would panic if Layout was invalid.
            Layout::from_size_align_unchecked(
                self.inner.capacity.load(Ordering::Acquire),
                self.inner.alignment,
            )
        }
    }

    /// Returns `true` if provided generic type `T` can be stored without
    /// growing the container or a [`LockingError::Poisoned`] error if
    /// allocation tracker mutex has been poisoned.
    ///
    /// This function will block the current thread until internal allocation
    /// tracker doesn't become available.
    pub fn can_push<T>(&self) -> Result<bool, LockingError> {
        let layout = Layout::new::<T>();
        let tracker = self
            .inner
            .tracker
            .lock_named(LockTarget::AllocationTracker)?;
        Ok(tracker.peek_next(layout).is_some())
    }

    /// Returns `true` if the provided `value` can be stored without growing the
    /// container or a [`LockingError::Poisoned`] error if allocation tracker
    /// mutex has been poisoned.
    ///
    /// This function will block the current thread until internal allocation
    /// tracker doesn't become available.
    pub fn can_push_value<T>(&self, value: &T) -> Result<bool, LockingError> {
        let layout = Layout::for_value(value);
        let tracker = self
            .inner
            .tracker
            .lock_named(LockTarget::AllocationTracker)?;
        Ok(tracker.peek_next(layout).is_some())
    }

    /// Returns `true` if the provided `layout` can be stored without growing
    /// the container or a [`LockingError::Poisoned`] error if allocation
    /// tracker mutex has been poisoned.
    ///
    /// This function will block the current thread until internal allocation
    /// tracker doesn't become available.
    pub fn can_push_layout(&self, layout: Layout) -> Result<bool, LockingError> {
        let tracker = self
            .inner
            .tracker
            .lock_named(LockTarget::AllocationTracker)?;
        Ok(tracker.peek_next(layout).is_some())
    }

    /// Resizes the memory container to the specified `new_capacity`, optionally
    /// returning the new base address of the stored items - if `None` is
    /// returned the base address of the memory block is the same.
    ///
    /// This function will block the current thread.
    ///
    /// # Errors
    ///
    /// [`ContiguousMemoryError::Unshrinkable`] error is returned when
    /// attempting to shrink the memory container, but previously stored data
    /// prevents the container from being shrunk to the desired capacity.
    ///
    /// [`ContiguousMemoryError::Lock`] is returned if the mutex holding the
    /// base address or the allocation tracker is poisoned.
    pub fn resize(
        &mut self,
        new_capacity: usize,
    ) -> Result<Option<BasePtr>, ContiguousMemoryError> {
        let old_capacity = self.get_capacity();
        if new_capacity == old_capacity {
            return Ok(None);
        }

        let mut tracker = self
            .inner
            .tracker
            .lock_named(LockTarget::AllocationTracker)?;
        let mut base = self.inner.base.write_named(LockTarget::BaseAddress)?;

        let old_layout = self.get_layout();
        let new_layout = Layout::from_size_align(new_capacity, old_layout.align())?;
        let prev_base = *base;
        *base = unsafe {
            if new_capacity > old_capacity {
                self.inner.alloc.grow(*base, old_layout, new_layout)?
            } else {
                self.inner.alloc.shrink(*base, old_layout, new_layout)?
            }
        };
        self.inner.capacity.store(new_capacity, Ordering::Release);

        tracker.resize(new_capacity)?;

        Ok(if *base != prev_base {
            Some(base.unwrap_or_else(|| unsafe { null_base(new_layout.align()) }))
        } else {
            None
        })
    }

    /// Reserves exactly `additional` bytes.
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + additional`.
    ///
    /// This function will block the current thread.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes or allocation of
    /// additional memory fails.
    ///
    /// # Errors
    ///
    /// [`LockingError::Poisoned`] is returned if the mutex holding the
    /// base address or the allocation tracker is poisoned.
    pub fn reserve(&mut self, additional: usize) -> Result<Option<BasePtr>, LockingError> {
        if additional == 0 {
            return Ok(None);
        }

        let old_capacity = self.get_capacity();
        let new_capacity = old_capacity.saturating_add(additional);

        let mut tracker = self
            .inner
            .tracker
            .lock_named(LockTarget::AllocationTracker)?;
        let mut base = self.inner.base.write_named(LockTarget::BaseAddress)?;

        let old_layout = self.get_layout();
        let new_layout = Layout::from_size_align(new_capacity, old_layout.align())
            .expect("new capacity exceeds `isize::MAX`");
        let prev_base = *base;
        *base = unsafe { self.inner.alloc.grow(*base, old_layout, new_layout) }
            .expect("unable to allocate required memory");
        self.inner.capacity.store(new_capacity, Ordering::Release);

        tracker.grow(new_capacity);

        Ok(if *base != prev_base {
            Some(base.unwrap_or_else(|| unsafe { null_base(new_layout.align()) }))
        } else {
            None
        })
    }

    /// Reserves additional bytes required to store a value with provided
    /// `layout` while keeping it aligned (required padding bytes at the end of
    /// the container will be included).
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + padding + size_of::<V>()`.
    ///
    /// This function will block the current thread.
    ///
    /// # Errors
    ///
    /// [`LockingError::Poisoned`] is returned if the mutex holding the
    /// base address or the allocation tracker is poisoned.
    pub fn reserve_layout(&mut self, layout: Layout) -> Result<Option<BasePtr>, LockingError> {
        if layout.size() == 0 {
            return Ok(None);
        }

        match self.get_base()? {
            Some(it) => {
                let mut tracker = self
                    .inner
                    .tracker
                    .lock_named(LockTarget::AllocationTracker)?;

                let old_capacity = tracker.len();
                let last = unsafe { (it.as_ptr() as *mut u8).add(old_capacity) };
                let align_offset = last.align_offset(layout.align());
                let new_capacity = old_capacity.saturating_add(align_offset + layout.size());

                let mut base = self.inner.base.write_named(LockTarget::BaseAddress)?;

                let old_layout = self.get_layout();
                let new_layout = Layout::from_size_align(new_capacity, old_layout.align())
                    .expect("new capacity exceeds `isize::MAX`");
                let prev_base = *base;
                *base = unsafe { self.inner.alloc.grow(*base, old_layout, new_layout) }
                    .expect("unable to allocate required memory");
                self.inner.capacity.store(new_capacity, Ordering::Release);

                tracker.grow(new_capacity);

                Ok(if *base != prev_base {
                    Some(base.unwrap_or_else(|| unsafe { null_base(new_layout.align()) }))
                } else {
                    None
                })
            }
            None => self.reserve(layout.size()),
        }
    }

    /// Shrinks the allocated memory to fit the currently stored data and
    /// returns the new capacity.
    ///
    /// This function will block the current thread until internal allocation
    /// tracker doesn't become available.
    pub fn shrink_to_fit(&mut self) -> Result<BaseAddress, LockingError> {
        let shrink_result = self
            .inner
            .tracker
            .lock_named(LockTarget::AllocationTracker)?
            .shrink_to_fit();

        if let Some(new_capacity) = shrink_result {
            let mut base = self.inner.base.write_named(LockTarget::BaseAddress)?;

            let old_layout = self.get_layout();
            let new_layout = unsafe {
                // SAFETY: Previous layout was valid and had valid alignment,
                // new one is smaller with same alignment so it must be
                // valid as well.
                Layout::from_size_align_unchecked(new_capacity, old_layout.align())
            };

            *base = unsafe {
                self.inner
                    .alloc
                    .shrink(*base, self.get_layout(), new_layout)
            }
            .expect("unable to shrink allocated memory");
            self.inner.capacity.store(new_capacity, Ordering::Release);

            Ok(*base)
        } else {
            self.get_base()
        }
    }

    /// Stores a `value` of type `T` in the contiguous memory block and returns
    /// a [`SyncContiguousEntryRef<T>`](SyncContiguousEntryRef) pointing
    /// to it.
    ///
    /// Value type argument `T` is used to deduce type size and returned
    /// reference dropping behavior.
    ///
    /// # Errors
    ///
    /// A [`LockingError::Poisoned`](crate::error::LockingError::Poisoned) error
    /// is returned when the allocation tracker of the container is poisoned.
    pub fn push<T>(&mut self, value: T) -> Result<SyncContiguousEntryRef<T, A>, LockingError> {
        let mut data = ManuallyDrop::new(value);
        let layout = Layout::for_value(&data);
        let pos = &mut *data as *mut T;

        unsafe { self.push_raw(pos, layout) }
    }

    /// Stores a `value` of type `T` in the contiguous memory block and returns
    /// a reference to it which doesn't mark the memory segment as free when
    /// dropped.
    ///
    /// # Errors
    ///
    /// A [`LockingError::Poisoned`](crate::error::LockingError::Poisoned) error
    /// is returned when the allocation tracker of the container is poisoned.
    pub fn push_persisted<T>(
        &mut self,
        value: T,
    ) -> Result<SyncContiguousEntryRef<T, A>, LockingError> {
        let mut data = ManuallyDrop::new(value);
        let layout = Layout::for_value(&data);
        let pos = &mut *data as *mut T;

        unsafe { self.push_raw_persisted(pos, layout) }
    }

    /// Works same as [`push`](SyncContiguousMemory::push) but takes a pointer
    /// and layout.
    ///
    /// Pointer type is used to deduce the destruction behavior for
    /// implementations that return a reference, but can be disabled by casting
    /// the provided pointer into `*const ()` type and then calling
    /// [`transmute`](core::mem::transmute) on the returned reference.
    /// ([_example_](crate::ContigousMemory::push_raw))
    ///
    /// # Safety
    ///
    /// This function is unsafe because it clones memory from provided pointer
    /// which means it could cause a segmentation fault if the pointer is
    /// invalid.
    ///
    /// Further, it also allows escaping type drop glue because it takes type
    /// [`Layout`] as a separate argument.
    pub unsafe fn push_raw<T>(
        &mut self,
        data: *const T,
        layout: Layout,
    ) -> Result<SyncContiguousEntryRef<T, A>, LockingError> {
        let mut tracker = self
            .inner
            .tracker
            .lock_named(LockTarget::AllocationTracker)?;

        let range = loop {
            let base = self.get_base()?;
            match tracker.take_next(base, layout) {
                Ok(taken) => {
                    let found = taken.offset_base_unwrap(base) as *mut u8;
                    unsafe { core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size()) }
                    break taken;
                }
                Err(ContiguousMemoryError::NoStorageLeft) => {
                    let mut base_guard = self.inner.base.write_named(LockTarget::BaseAddress)?;
                    match base {
                        Some(prev_base) => {
                            let curr_capacity = self.inner.capacity.load(Ordering::Acquire);

                            let start_free =
                                (prev_base.as_ptr() as *const u8).add(tracker.last_offset());
                            let padding = start_free.align_offset(layout.align());
                            let increment = padding + layout.size() - tracker.tailing_free_bytes();

                            let new_capacity = curr_capacity
                                .saturating_mul(2)
                                .max(curr_capacity + increment);

                            tracker.grow(new_capacity);

                            let old_layout = self.get_layout();
                            let new_layout =
                                Layout::from_size_align(new_capacity, old_layout.align())
                                    .expect("new capacity exceeds `isize::MAX`");
                            *base_guard = unsafe {
                                self.inner.alloc.grow(*base_guard, old_layout, new_layout)
                            }
                            .expect("unable to allocate required memory");
                            self.inner.capacity.store(new_capacity, Ordering::Release);
                        }
                        None => {
                            tracker.grow(layout.size());
                            *base_guard = self
                                .inner
                                .alloc
                                .allocate(layout)
                                .expect("pushed element size exceeds `isize::MAX`");
                            self.inner.capacity.store(layout.size(), Ordering::Release);
                        }
                    }
                }
                Err(ContiguousMemoryError::Lock(locking_err)) => return Err(locking_err),
                Err(other) => unreachable!(
                    "reached unexpected error while looking for next region to store data: {:?}",
                    other
                ),
            }
        };

        Ok(SyncContiguousEntryRef {
            inner: Arc::new(ReferenceState {
                state: self.inner.clone(),
                range,
                borrow_kind: RwLock::new(()),
                drop_fn: drop_fn::<T>(),
                _phantom: PhantomData,
            }),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        })
    }

    /// Variant of [`push_raw`](SyncContiguousMemory::push_raw) which returns a
    /// reference that never marks the used memory segment as free when
    /// dropped.
    pub unsafe fn push_raw_persisted<T>(
        &mut self,
        data: *const T,
        layout: Layout,
    ) -> Result<SyncContiguousEntryRef<T, A>, LockingError> {
        match self.push_raw(data, layout) {
            Ok(it) => {
                let result = it.clone();
                core::mem::forget(it.inner);
                Ok(result)
            }
            err => err,
        }
    }

    /// Assumes value is stored at the provided _relative_ `position` in
    /// managed memory and returns a pointer or a reference to it.
    ///
    /// # Example
    ///
    /// TODO: Add Sync assume_stored example
    ///
    /// # Safety
    ///
    /// This functions isn't unsafe because creating an invalid pointer isn't
    /// considered unsafe. Responsibility for guaranteeing safety falls on
    /// code that's dereferencing the pointer.
    pub fn assume_stored<T>(
        &self,
        position: usize,
    ) -> Result<SyncContiguousEntryRef<T, A>, LockingError> {
        Ok(SyncContiguousEntryRef {
            inner: Arc::new(ReferenceState {
                state: self.inner.clone(),
                range: ByteRange(position, position + size_of::<T>()),
                borrow_kind: RwLock::new(()),
                drop_fn: drop_fn::<T>(),
                _phantom: PhantomData,
            }),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        })
    }

    /// Clones the allocated memory region into a new SyncMemoryStorage.
    ///
    /// This function isn't unsafe, even though it ignores presence of `Copy`
    /// bound on stored data, because it doesn't create any invalid references.
    #[must_use]
    pub fn copy_data(&self) -> Result<Self, LockingError>
    where
        A: Clone,
    {
        let base = self.inner.base.read_named(LockTarget::BaseAddress)?;
        let current_layout = self.get_layout();
        let result = Self::new_with_layout_and_alloc(current_layout, self.inner.alloc.clone());
        match *base {
            Some(base) => unsafe {
                core::ptr::copy_nonoverlapping(
                    base.as_ptr() as *const (),
                    result
                        .get_base()
                        .unwrap_unchecked()
                        .unwrap_unchecked()
                        .as_ptr() as *mut (),
                    current_layout.size(),
                );
            },
            None => {
                // empty structure; nothing to copy
            }
        }

        Ok(result)
    }

    /// Marks the entire contents of the container as free, allowing new data
    /// to be stored in place of previously stored data.
    ///
    /// This allows clearing persisted entries created with
    /// [`SyncContiguousMemory::push_persisted`] and
    /// [`SyncContiguousMemory::push_raw_persisted`] methods.
    ///
    /// See also:
    /// - [`SyncContiguousMemory::clear_region`] - for freeing a specific
    ///   container region
    ///
    /// # Errors
    ///
    /// A [`LockingError::Poisoned`](crate::error::LockingError::Poisoned) error
    /// is returned when the allocation tracker of the container is poisoned.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it doesn't invalidate any previously
    /// returned references. Storing data into the container and then trying to
    /// access previously stored data from any existing references will cause
    /// undefined behavior.
    pub unsafe fn clear(&mut self) -> Result<(), LockingError> {
        self.inner
            .tracker
            .lock_named(LockTarget::AllocationTracker)?
            .clear();
        Ok(())
    }

    /// Marks the provided `region` of the container as free, allowing new data
    /// to be stored in place of previously stored data.
    ///
    /// This allows clearing persisted entries created with
    /// [`SyncContiguousMemory::push_persisted`] and
    /// [`SyncContiguousMemory::push_raw_persisted`] methods.
    ///
    /// See also:
    /// - [`SyncContiguousMemory::clear`] - for freeing the entire container
    ///
    /// # Errors
    ///
    /// A [`ContiguousMemoryError::NotContained`] error is returned if the
    /// provided region falls outside of the memory tracked by the allocation
    /// tracker.
    ///
    /// A [`LockingError::Poisoned`](crate::error::LockingError::Poisoned) error
    /// is returned when the allocation tracker of the container is poisoned.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it doesn't invalidate any previously
    /// returned references overlapping `region`. Storing data into the
    /// container and then trying to access previously stored data from
    /// overlapping regions will cause undefined behavior.
    pub unsafe fn clear_region(&mut self, region: ByteRange) -> Result<(), ContiguousMemoryError> {
        self.inner
            .tracker
            .lock_named(LockTarget::AllocationTracker)?
            .release(region)
    }

    /// Forgets this container without dropping it and returns its base address
    /// and [`Layout`], or a [`LockingError::Poisoned`] error if base address
    /// `RwLock` has been poisoned.
    ///
    /// For details on safety see _Safety_ section of
    /// [default implementation](crate::ContiguousMemory::forget).
    pub fn forget(self) -> Result<(BaseAddress, Layout), LockingError> {
        let base = self.get_base()?;
        let layout = self.get_layout();
        core::mem::forget(self);
        Ok((base, layout))
    }
}

#[cfg(feature = "debug")]
impl core::fmt::Debug for SyncContiguousMemory
where
    MemoryState<ImplConcurrent>: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SyncContiguousMemory")
            .field("inner", &self.inner)
            .finish()
    }
}
