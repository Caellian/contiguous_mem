use core::alloc::{Layout, LayoutError};
use core::marker::PhantomData;
use core::mem::{size_of, ManuallyDrop};

use crate::error::{ContiguousMemoryError, LockSource, LockingError};
use crate::refs::sealed::ReferenceState;
pub use crate::refs::SyncContiguousEntryRef;
use crate::sealed::MemoryState;
use crate::types::*;
use crate::{ByteRange, ImplConcurrent};

/// A collection that can store different data types in a contigous block of
/// memory.
///
/// Note that copying this structure creates a copy which represents the same
/// internal state. If you need to copy the memory region into a new container
/// see: [`SyncContiguousMemory::copy_data`]
///
/// # Example
///
/// ```rust
#[doc = include_str!("../examples/sync_impl.rs")]
/// ```
#[derive(Clone)]
pub struct SyncContiguousMemory {
    inner: Arc<MemoryState<ImplConcurrent>>,
}

impl SyncContiguousMemory {
    /// Creates a new `ContiguousMemory` instance with the specified `capacity`,
    /// aligned as platform dependant alignment of `usize`.
    pub fn new(capacity: usize) -> Self {
        Self::new_aligned(capacity, core::mem::align_of::<usize>())
            .expect("unable to create a ContiguousMemory with usize alignment")
    }

    /// Creates a new `ContiguousMemory` instance with the specified `capacity`
    /// and `alignment`.
    pub fn new_aligned(capacity: usize, alignment: usize) -> Result<Self, LayoutError> {
        let layout = Layout::from_size_align(capacity, alignment)?;
        let base = unsafe { allocator::alloc(layout) };

        Ok(Self {
            inner: MemoryState::new_concurrent(base, capacity, alignment),
        })
    }

    /// Creates a new `ContiguousMemory` instance with the provided `layout`.
    pub fn new_for_layout(layout: Layout) -> Self {
        let base = unsafe { allocator::alloc(layout) };
        Self {
            inner: MemoryState::new_concurrent(base, layout.size(), layout.align()),
        }
    }

    /// Returns the base address of the allocated memory or a
    /// [`LockingError::Poisoned`] error if the mutex holding the base address
    /// has been poisoned.
    ///
    /// This function will block the current thread until base address RwLock
    /// doesn't become readable.
    #[inline]
    pub fn get_base(&self) -> Result<*const (), LockingError> {
        Ok(*self.inner.base.read_named(LockSource::BaseAddress)? as *const ())
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
            .lock_named(LockSource::AllocationTracker)?;
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
            .lock_named(LockSource::AllocationTracker)?;
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
            .lock_named(LockSource::AllocationTracker)?;
        Ok(tracker.peek_next(layout).is_some())
    }

    /// Resizes the memory container to the specified `new_capacity`, optionally
    /// returning the new base address of the stored items - if `None` is
    /// returned the base address of the memory block is the same.
    ///
    /// Shrinking the container is generally performed in place by freeing
    /// tailing memory space, but growing it can move the data in memory to find
    /// a location that can fit it.
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
    ) -> Result<Option<*const ()>, ContiguousMemoryError> {
        let old_capacity = self.get_capacity();
        if new_capacity == old_capacity {
            return Ok(None);
        }

        let mut tracker = self
            .inner
            .tracker
            .lock_named(LockSource::AllocationTracker)?;
        let mut base = self.inner.base.write_named(LockSource::BaseAddress)?;

        let prev_addr = *base;
        *base = unsafe { allocator::realloc(*base, self.get_layout(), new_capacity) };
        self.inner.capacity.store(new_capacity, Ordering::Release);

        tracker.resize(new_capacity)?;

        Ok(if *base != prev_addr {
            Some(*base as *const ())
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
    /// # Errors
    ///
    /// [`LockingError::Poisoned`] is returned if the mutex holding the
    /// base address or the allocation tracker is poisoned.
    pub fn reserve(&mut self, additional: usize) -> Result<Option<*const ()>, LockingError> {
        match self.resize(self.get_capacity() + additional) {
            Ok(it) => Ok(it),
            Err(ContiguousMemoryError::Lock(err)) => Err(err),
            Err(other) => unreachable!("unable to grow the container: {:?}", other),
        }
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
    pub fn reserve_layout(&mut self, layout: Layout) -> Result<Option<*const ()>, LockingError> {
        let mut tracker = self
            .inner
            .tracker
            .lock_named(LockSource::AllocationTracker)?;
        let mut base = self.inner.base.write_named(LockSource::BaseAddress)?;

        let last = unsafe { base.add(tracker.len()) };
        let align_offset = last.align_offset(layout.align());
        let new_capacity = align_offset + layout.size();

        let prev_addr = *base;
        *base = unsafe { allocator::realloc(*base, self.get_layout(), new_capacity) };
        self.inner.capacity.store(new_capacity, Ordering::Release);

        tracker
            .resize(new_capacity)
            .expect("unable to grow the container");

        Ok(if *base != prev_addr {
            Some(*base as *const ())
        } else {
            None
        })
    }

    /// Reserves exactly additional bytes required to store a value of type `V`.
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + size_of::<V>()`.
    ///
    /// This function will block the current thread.
    ///
    /// # Errors
    ///
    /// [`LockingError::Poisoned`] is returned if the mutex holding the
    /// base address or the allocation tracker is poisoned.
    #[inline]
    pub fn reserve_type<V>(&mut self) -> Result<Option<*const ()>, LockingError> {
        self.reserve_layout(Layout::new::<V>())
    }

    /// Reserves exactly additional bytes required to store `count` number of
    /// values of type `V`.
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + size_of::<V>() * count`.
    ///
    /// This function will block the current thread.
    ///
    /// # Errors
    ///
    /// [`LockingError::Poisoned`] is returned if the mutex holding the
    /// base address or the allocation tracker is poisoned.
    pub fn reserve_type_count<V>(
        &mut self,
        count: usize,
    ) -> Result<Option<*const ()>, LockingError> {
        let mut tracker = self
            .inner
            .tracker
            .lock_named(LockSource::AllocationTracker)?;
        let mut base = self.inner.base.write_named(LockSource::BaseAddress)?;

        let layout = Layout::new::<V>();
        let last = unsafe { base.add(tracker.len()) };
        let align_offset = last.align_offset(layout.align());
        let inner_padding = unsafe {
            last.add(align_offset + layout.size())
                .align_offset(layout.align())
        };
        let new_capacity =
            align_offset + layout.size() * count + inner_padding * count.saturating_sub(1);

        let prev_addr = *base;
        *base = unsafe { allocator::realloc(*base, self.get_layout(), new_capacity) };
        self.inner.capacity.store(new_capacity, Ordering::Release);

        tracker
            .resize(new_capacity)
            .expect("unable to grow the container");

        Ok(if *base != prev_addr {
            Some(*base as *const ())
        } else {
            None
        })
    }

    /// Shrinks the allocated memory to fit the currently stored data and
    /// returns the new capacity.
    ///
    /// This function will block the current thread until internal allocation
    /// tracker doesn't become available.
    pub fn shrink_to_fit(&mut self) -> Result<usize, LockingError> {
        let shrink_result = self
            .inner
            .tracker
            .lock_named(LockSource::AllocationTracker)?
            .shrink_to_fit();

        if let Some(new_capacity) = shrink_result {
            let mut base = self.inner.base.write_named(LockSource::BaseAddress)?;
            *base = unsafe { allocator::realloc(*base, self.get_layout(), new_capacity) };
            self.inner.capacity.store(new_capacity, Ordering::Release);

            Ok(new_capacity)
        } else {
            Ok(self.get_capacity())
        }
    }

    /// Stores a `value` of type `T` in the contiguous memory block and returns
    /// a [`SyncContiguousEntryRef<T>`](refs::SyncContiguousEntryRef) pointing
    /// to it.
    ///
    /// Value type argument `T` is used to deduce type size and returned
    /// reference dropping behavior.
    ///
    /// # Errors
    ///
    /// A [`LockingError::Poisoned`](crate::error::LockingError::Poisoned) error
    /// is returned when the allocation tracker of the container is poisoned.
    pub fn push<T>(&mut self, value: T) -> Result<SyncContiguousEntryRef<T>, LockingError> {
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
    ) -> Result<SyncContiguousEntryRef<T>, LockingError> {
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
    /// [`transmute`](core::mem::transmute) on the returned reference:
    /// ```rust
    /// # use contiguous_mem::{ContiguousMemory, CERef};
    /// # use core::alloc::Layout;
    /// # use core::mem;
    /// # let mut storage = ContiguousMemory::new(0);
    /// let value = vec!["ignore", "drop", "for", "me"];
    /// let erased = &value as *const Vec<&str> as *const ();
    /// let layout = Layout::new::<Vec<&str>>();
    ///
    /// let stored: CERef<Vec<&str>> = unsafe {
    ///     mem::transmute(storage.push_raw(erased, layout))
    /// };
    /// ```
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
    ) -> Result<SyncContiguousEntryRef<T>, LockingError> {
        let mut tracker = self
            .inner
            .tracker
            .lock_named(LockSource::AllocationTracker)?;

        let range = loop {
            let base = self.get_base()? as usize;
            match tracker.take_next(base, layout) {
                Ok(taken) => {
                    let found = (taken.0 + base) as *mut u8;
                    unsafe { core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size()) }
                    break taken;
                }
                Err(ContiguousMemoryError::NoStorageLeft) => {
                    let curr_capacity = self.inner.capacity.load(Ordering::Acquire);

                    let mut base = self.inner.base.write_named(LockSource::BaseAddress)?;

                    let start_free = base.add(tracker.last_offset());
                    let padding = start_free.align_offset(layout.align());
                    let increment = padding + layout.size() - tracker.tailing_free_bytes();

                    let new_capacity = curr_capacity
                        .saturating_mul(2)
                        .max(curr_capacity + increment);

                    tracker
                        .resize(new_capacity)
                        .expect("unable to grow allocation tracker");

                    let storage_layout = unsafe {
                        Layout::from_size_align_unchecked(curr_capacity, self.inner.alignment)
                    };
                    let new_base =
                        unsafe { allocator::realloc(*base, storage_layout, new_capacity) };
                    *base = new_base;
                    self.inner.capacity.store(new_capacity, Ordering::Release);
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

    /// Variant of [`push_raw`](ContiguousMemory::push_raw) which returns a
    /// reference that never marks the used memory segment as free when
    /// dropped.
    pub unsafe fn push_raw_persisted<T>(
        &mut self,
        data: *const T,
        layout: Layout,
    ) -> Result<SyncContiguousEntryRef<T>, LockingError> {
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
    /// ```rust
    /// # use contiguous_mem::UnsafeContiguousMemory;
    /// let mut storage = UnsafeContiguousMemory::new(128);
    /// let initial_position = storage.push(278u32).unwrap();
    ///
    /// // ...other code...
    ///
    /// let base_addr = storage.get_base();
    /// storage.resize(512);
    ///
    /// let new_position: *mut u32 = storage.assume_stored(
    ///     initial_position as usize - base_addr as usize
    /// );
    /// unsafe {
    ///     assert_eq!(*new_position, 278u32);
    /// }
    /// ```
    ///
    /// # Safety
    ///
    /// This functions isn't unsafe because creating an invalid pointer isn't
    /// considered unsafe. Responsibility for guaranteeing safety falls on
    /// code that's dereferencing the pointer.
    pub fn assume_stored<T>(
        &self,
        position: usize,
    ) -> Result<SyncContiguousEntryRef<T>, LockingError> {
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

    /// Marks the entire contents of the container as free, allowing new data
    /// to be stored in place of previously stored data.
    ///
    /// This allows clearing persisted entries created with
    /// [`ContiguousMemory::push_persisted`] and
    /// [`ContiguousMemory::push_raw_persisted`] methods.
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
            .lock_named(LockSource::AllocationTracker)?
            .clear();
        Ok(())
    }

    /// Marks the provided `region` of the container as free, allowing new data
    /// to be stored in place of previously stored data.
    ///
    /// This allows clearing persisted entries created with
    /// [`ContiguousMemory::push_persisted`] and
    /// [`ContiguousMemory::push_raw_persisted`] methods.
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
    pub unsafe fn clear_region(
        &mut self,
        region: ByteRange,
    ) -> Result<(), ContiguousMemoryError> {
        self.inner
            .tracker
            .lock_named(LockSource::AllocationTracker)?
            .release(region)
    }

    /// Forgets this container without dropping it and returns its base address
    /// and [`Layout`], or a [`LockingError::Poisoned`] error if base address
    /// `RwLock` has been poisoned.
    ///
    /// For details on safety see _Safety_ section of
    /// [default implementation](ContiguousMemoryStorage<ImplDefault>::forget).
    pub fn forget(self) -> Result<(*const (), Layout), LockingError> {
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
