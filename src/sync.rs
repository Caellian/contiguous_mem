use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem::{align_of, size_of, ManuallyDrop};

use crate::common::*;
use crate::error::{LockTarget, LockingError, MemoryError, SyncMemoryError};
use crate::memory::{DefaultMemoryManager, ManageMemory};
use crate::range::ByteRange;
use crate::raw::*;
use crate::refs::{sealed::ReferenceState, SyncContiguousEntryRef};
use crate::types::*;
use crate::ImplConcurrent;

/// A synchronized version of [`ContiguousMemory`](crate::ContiguousMemory),
/// refer to it for usage examples.
///
/// All container functions are blocking and return a [`LockingError`] if
/// required parts of the container can't be locked due to poisoning. That is,
/// [`LockingError::Poisoned`] variant is always returned in case of errors.
///
/// # Examples
///
/// ```
#[doc = include_str!("../examples/sync_impl.rs")]
/// ```
pub struct SyncContiguousMemory<A: ManageMemory = DefaultMemoryManager> {
    inner: Arc<MemoryState<ImplConcurrent, A>>,
}

impl SyncContiguousMemory {
    /// Creates a new, empty `SyncContiguousMemory` instance aligned with
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
    pub fn with_capacity(capacity: usize) -> Self {
        if !is_layout_valid(capacity, align_of::<usize>()) {
            panic!(
                "capacity too large; max: {}",
                isize::MAX as usize - (align_of::<usize>() - 1)
            )
        }
        Self::with_layout(unsafe {
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
    pub fn with_layout(layout: Layout) -> Self {
        Self {
            inner: match MemoryState::new_sync(layout) {
                Ok(it) => it,
                Err(_) => unreachable!("unable to create a container with layout: {:?}", layout),
            },
        }
    }
}

impl<A: ManageMemory> SyncContiguousMemory<A> {
    /// Creates a new, empty `SyncContiguousMemory` instance aligned with
    /// alignment of `usize` that uses the specified allocator.
    pub fn with_alloc(alloc: A) -> Self {
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
    pub fn with_capacity_and_alloc(capacity: usize, alloc: A) -> Self {
        if !is_layout_valid(capacity, align_of::<usize>()) {
            panic!(
                "capacity too large; max: {}",
                isize::MAX as usize - (align_of::<usize>() - 1)
            )
        }
        unsafe {
            Self::with_layout_and_alloc(
                Layout::from_size_align_unchecked(capacity, align_of::<usize>()),
                alloc,
            )
        }
    }

    /// Creates a new `SyncContiguousMemory` instance with capacity and
    /// alignment of the provided `layout`.
    ///
    /// # Panics
    ///
    /// Panics if the allocator can't provide required amount of memory.
    pub fn with_layout_and_alloc(layout: Layout, alloc: A) -> Self {
        Self {
            inner: match MemoryState::new_sync_with_alloc(layout, alloc) {
                Ok(it) => it,
                Err(_) => panic!("unable to create a container with layout: {:?}", layout),
            },
        }
    }

    /// Returns the base address of the allocated memory or an error if the
    /// mutex holding the base address has been poisoned.
    ///
    /// This function will block the current thread until base address RwLock
    /// doesn't become readable.
    #[inline]
    pub fn base(&self) -> Result<BaseAddress, LockingError> {
        self.inner
            .base
            .read_named(LockTarget::BaseAddress)
            .map(|it| *it)
    }

    /// Returns a pointer to the base address of the allocated memory or `null`
    /// if the container didn't allocate.
    ///
    /// [`LockingError::Poisoned`] error is returned if the mutex holding the
    /// base address has been poisoned.
    pub fn base_ptr(&self) -> Result<*const u8, LockingError> {
        match self.base()? {
            Some(it) => Ok(it.as_ptr() as *const u8),
            None => Ok(core::ptr::null()),
        }
    }

    /// Returns the current capacity of the memory container.
    ///
    /// The capacity represents the size of the memory block that has been
    /// allocated for storing data. It may be larger than the amount of data
    /// currently stored within the container.
    #[inline]
    pub fn capacity(&self) -> Result<usize, LockingError> {
        Ok(match self.base()? {
            Some(it) => unsafe { it.as_ref().len() },
            None => 0,
        })
    }

    /// Returns the total size of all stored entries excluding the padding or a
    /// [`LockingError::Poisoned`] if segment tracker mutex has been
    /// poisoned.
    pub fn size(&self) -> Result<usize, LockingError> {
        let free_bytes = self
            .inner
            .tracker
            .lock_named(LockTarget::SegmentTracker)?
            .count_free();
        Ok(self.capacity()? - free_bytes)
    }

    /// Returns the alignment of the memory container.
    #[inline]
    pub fn align(&self) -> usize {
        self.inner.alignment
    }

    /// Returns the layout of the memory region containing stored data.
    #[inline]
    pub fn layout(&self) -> Result<Layout, LockingError> {
        Ok(unsafe {
            // SAFETY: Constructor would panic if Layout was invalid.
            base_addr_layout(self.base()?, self.align())
        })
    }

    /// Returns `true` if provided generic type `T` can be stored without
    /// growing the container or a [`LockingError::Poisoned`] error if
    /// segment tracker mutex has been poisoned.
    ///
    /// This function will block the current thread until internal allocation
    /// tracker doesn't become available.
    #[inline]
    pub fn can_push_t<T>(&self) -> Result<bool, LockingError> {
        self.can_push(Layout::new::<T>())
    }

    /// Returns `true` if the provided `value` can be stored without growing the
    /// container or a [`LockingError::Poisoned`] error if segment tracker
    /// mutex has been poisoned.
    ///
    /// `value` can either be a [`Layout`] or a reference to a `Sized` value.
    pub fn can_push(&self, value: impl HasLayout) -> Result<bool, LockingError> {
        let layout = value.as_layout();
        let tracker = self.inner.tracker.lock_named(LockTarget::SegmentTracker)?;
        let base = self.base()?;
        Ok(tracker.can_store(base, layout))
    }

    /// Grows the memory container to the specified `new_capacity`, optionally
    /// returning the new base address and size of the underlying memory or a
    /// `LockingError` if the segment tracker `Mutex` or base address
    /// `RwLock` has been poisoned.
    ///
    /// If the base address of the memory block stays the same the returned
    /// value is `None`. If `new_capacity` is 0, the retuned pointer will be an
    /// invalid pointer with container alignment.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` or the allocator
    /// operation fails.
    pub fn grow_to(&mut self, new_capacity: usize) -> Result<Option<BasePtr>, LockingError> {
        match self.try_grow_to(new_capacity) {
            Ok(it) => Ok(it),
            Err(SyncMemoryError::Memory(MemoryError::TooLarge)) => {
                panic!("new capacity exceeds `isize::MAX`")
            }
            Err(SyncMemoryError::Memory(MemoryError::Allocator(_))) => panic!("allocator error"),
            Err(SyncMemoryError::Lock(err)) => Err(err),
        }
    }

    /// Tries growing the memory container to the specified `new_capacity`,
    /// optionally returning the new base address and size of the underlying
    /// memory, or a [`SyncMemoryError`] if the new capacity exceeds
    /// `isize::MAX`, the allocator can't allocate required memory, or a
    /// Mutex/RwLock has been poisoned.
    ///
    /// If the base address of the memory block stays the same the returned
    /// value is `None`.
    pub fn try_grow_to(&mut self, new_capacity: usize) -> Result<Option<BasePtr>, SyncMemoryError> {
        let mut tracker = self.inner.tracker.lock_named(LockTarget::SegmentTracker)?;
        let mut base = self.inner.base.write_named(LockTarget::BaseAddress)?;

        let old_capacity = base_addr_capacity(*base);
        let new_capacity = tracker.grow(new_capacity);
        if new_capacity == old_capacity {
            return Ok(None);
        };

        let old_layout = unsafe { base_addr_layout(*base, self.inner.alignment) };
        let new_layout = Layout::from_size_align(new_capacity, old_layout.align())
            .map_err(|_| MemoryError::TooLarge)?;

        let prev_base = *base;
        *base = unsafe { self.inner.alloc.grow(*base, old_layout, new_layout)? };

        Ok(if *base != prev_base {
            Some(unsafe {
                // SAFETY: new_capacity must be > 0, because it's max of
                // old_capacity and passed argument, if both are 0 we return
                // early
                base.unwrap_unchecked()
            })
        } else {
            None
        })
    }

    /// Handles reserving capacity while ensuring appropriate padding.
    #[inline]
    fn ensure_free_section<const EXACT: bool>(
        &mut self,
        required: usize,
        align: Option<usize>,
    ) -> Result<Option<BasePtr>, SyncMemoryError> {
        let (capacity, last_offset, largest_free, tailing_free) = {
            let tracker = self.inner.tracker.lock_named(LockTarget::SegmentTracker)?;
            (
                tracker.size(),
                tracker.last_offset(),
                tracker.largest_free_range(),
                tracker.tailing_free_bytes(),
            )
        };
        let base_pos = self.base_ptr()? as usize;

        if let Some(largest) = largest_free {
            debug_assert!(base_pos != 0);

            let largest_size = align
                .map(|a| largest.offset(base_pos).aligned(a))
                .unwrap_or(largest)
                .len();

            if largest_size >= required {
                return Ok(None);
            }
        }

        let padding = match align {
            None => 0,
            Some(a) => {
                // we know that base + last_offset won't fall out of addressable
                // range because allocator would've already failed by this point
                let pos = if capacity > 0 {
                    base_pos + last_offset
                } else {
                    // if capacity is 0, we didn't allocate and only need to
                    // ensure relative alignment padding
                    self.align()
                };
                let extra = pos % a;

                // if already aligned padding is 0
                if extra > 0 {
                    a - extra
                } else {
                    0
                }
            }
        };

        let mut additional = required + padding - tailing_free;
        if !EXACT {
            additional = core::cmp::max(capacity, additional);
        }

        self.try_grow_to(capacity + additional)
    }

    /// Grows the underlying memory to ensure container has a free segment that
    /// can store `capacity`.
    /// This function might allocate more than requested amount of memory to
    /// reduce number of reallocations.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// [`LockingError::Poisoned`] is returned if the mutex holding the
    /// base address or the segment tracker is poisoned.
    ///
    /// After calling this function, new capacity will be greater than:
    /// `self.size() + capacity`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve(&mut self, capacity: usize) -> Result<Option<BasePtr>, LockingError> {
        match self.try_reserve(capacity) {
            Ok(it) => Ok(it),
            Err(SyncMemoryError::Memory(MemoryError::TooLarge)) => {
                panic!("new capacity exceeds `isize::MAX`")
            }
            Err(SyncMemoryError::Memory(MemoryError::Allocator(_))) => {
                panic!("unable to allocate more memory")
            }
            Err(SyncMemoryError::Lock(err)) => Err(err),
        }
    }

    /// Tries growing the underlying memory to ensure container has a free
    /// segment that can store `capacity`.
    /// This function might allocate more than requested amount of memory to
    /// reduce number of reallocations.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// If the new capacity exceeds `isize::MAX` or the allocator couldn't
    /// allocate required memory, a [`MemoryError`] is returned.
    /// [`LockingError::Poisoned`] is returned if the mutex holding the
    /// base address or the segment tracker is poisoned.
    ///
    /// After calling this function, new capacity will be greater than:
    /// `self.size() + capacity`.
    pub fn try_reserve(&mut self, capacity: usize) -> Result<Option<BasePtr>, SyncMemoryError> {
        if capacity == 0 {
            return Ok(None);
        }
        self.ensure_free_section::<false>(capacity, None)
    }

    /// Grows the underlying memory to ensure container has a free segment that
    /// can store `capacity`.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// [`LockingError::Poisoned`] is returned if the mutex holding the
    /// base address or the segment tracker is poisoned.
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.size() + capacity`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve_exact(&mut self, capacity: usize) -> Result<Option<BasePtr>, LockingError> {
        match self.try_reserve_exact(capacity) {
            Ok(it) => Ok(it),
            Err(SyncMemoryError::Memory(MemoryError::TooLarge)) => {
                panic!("new capacity exceeds `isize::MAX`")
            }
            Err(SyncMemoryError::Memory(MemoryError::Allocator(_))) => {
                panic!("unable to allocate more memory")
            }
            Err(SyncMemoryError::Lock(err)) => Err(err),
        }
    }

    /// Tries growing the underlying memory to ensure container has a free
    /// segment that can store `capacity`.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// If the new capacity exceeds `isize::MAX` or the allocator couldn't
    /// allocate required memory, a [`MemoryError`] is returned.
    /// [`LockingError::Poisoned`] is returned if the mutex holding the
    /// base address or the segment tracker is poisoned.
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.size() + capacity`.
    pub fn try_reserve_exact(
        &mut self,
        capacity: usize,
    ) -> Result<Option<BasePtr>, SyncMemoryError> {
        if capacity == 0 {
            return Ok(None);
        }
        self.ensure_free_section::<true>(capacity, None)
    }

    /// Grows the underlying memory to ensure container has a free segment that
    /// can store a value with provided `layout`.
    /// This function might allocate more than requested amount of memory to
    /// reduce number of reallocations.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// [`LockingError::Poisoned`] is returned if the mutex holding the
    /// base address or the segment tracker is poisoned.
    ///
    /// After calling this function, new capacity will be greater than:
    /// `self.size() + padding + size_of::<V>()`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve_layout(
        &mut self,
        layout: impl HasLayout,
    ) -> Result<Option<BasePtr>, LockingError> {
        match self.try_reserve_layout(layout) {
            Ok(it) => Ok(it),
            Err(SyncMemoryError::Memory(MemoryError::TooLarge)) => {
                panic!("new capacity exceeds `isize::MAX`")
            }
            Err(SyncMemoryError::Memory(MemoryError::Allocator(_))) => {
                panic!("unable to allocate more memory")
            }
            Err(SyncMemoryError::Lock(err)) => Err(err),
        }
    }

    /// Tries growing the underlying memory to ensure container has a free
    /// segment that can store a value with provided `layout`.
    /// This function might allocate more than requested amount of memory to
    /// reduce number of reallocations.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// If the new capacity exceeds `isize::MAX` or the allocator couldn't
    /// allocate required memory, a [`MemoryError`] is returned.
    /// [`LockingError::Poisoned`] is returned if the mutex holding the
    /// base address or the segment tracker is poisoned.
    ///
    /// After calling this function, new capacity will be greater than:
    /// `self.size() + padding + size_of::<V>()`.
    pub fn try_reserve_layout(
        &mut self,
        layout: impl HasLayout,
    ) -> Result<Option<BasePtr>, SyncMemoryError> {
        let layout = layout.as_layout();
        if layout.size() == 0 {
            return Ok(None);
        }
        self.ensure_free_section::<false>(layout.size(), Some(layout.align()))
    }

    /// Grows the underlying memory to ensure container has a free segment that
    /// can store a value with provided `layout`.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// [`LockingError::Poisoned`] is returned if the mutex holding the
    /// base address or the segment tracker is poisoned.
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.size() + padding + size_of::<V>()`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve_layout_exact(
        &mut self,
        layout: impl HasLayout,
    ) -> Result<Option<BasePtr>, LockingError> {
        match self.try_reserve_layout_exact(layout) {
            Ok(it) => Ok(it),
            Err(SyncMemoryError::Memory(MemoryError::TooLarge)) => {
                panic!("new capacity exceeds `isize::MAX`")
            }
            Err(SyncMemoryError::Memory(MemoryError::Allocator(_))) => {
                panic!("unable to allocate more memory")
            }
            Err(SyncMemoryError::Lock(err)) => Err(err),
        }
    }

    /// Tries growing the underlying memory to ensure container has a free
    /// segment that can store a value with provided `layout`.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// If the new capacity exceeds `isize::MAX` or the allocator couldn't
    /// allocate required memory, a [`MemoryError`] is returned.
    /// [`LockingError::Poisoned`] is returned if the mutex holding the
    /// base address or the segment tracker is poisoned.
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.size() + padding + layout.size()`.
    pub fn try_reserve_layout_exact(
        &mut self,
        layout: impl HasLayout,
    ) -> Result<Option<BasePtr>, SyncMemoryError> {
        let layout = layout.as_layout();
        if layout.size() == 0 {
            return Ok(None);
        }
        self.ensure_free_section::<true>(layout.size(), Some(layout.align()))
    }

    /// Shrinks the capacity with a lower bound and returns the base pointer.
    ///
    /// # Panics
    ///
    /// Panics if the allocator wasn't able to shrink the allocated memory
    /// region.
    pub fn shrink_to(&mut self, new_capacity: usize) -> Result<BaseAddress, LockingError> {
        let mut tracker = self.inner.tracker.lock_named(LockTarget::SegmentTracker)?;
        let new_capacity = tracker.shrink(new_capacity);

        let mut base = self.inner.base.write_named(LockTarget::BaseAddress)?;

        let old_layout = unsafe { base_addr_layout(*base, self.inner.alignment) };
        if new_capacity == old_layout.size() {
            return Ok(*base);
        }
        let new_layout = unsafe {
            // SAFETY: Previous layout was valid and had valid alignment,
            // new one is smaller with same alignment so it must be
            // valid as well.
            Layout::from_size_align_unchecked(new_capacity, old_layout.align())
        };

        let new_base = unsafe { self.inner.alloc.shrink(*base, old_layout, new_layout) }
            .expect("unable to shrink the container");
        *base = new_base;

        Ok(new_base)
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
            .lock_named(LockTarget::SegmentTracker)?
            .shrink_to_fit();

        let new_capacity = match shrink_result {
            Some(it) => it,
            None => return self.base(),
        };

        let mut base = self.inner.base.write_named(LockTarget::BaseAddress)?;

        let old_layout = unsafe { base_addr_layout(*base, self.inner.alignment) };
        let new_layout = unsafe {
            // SAFETY: Previous layout was valid and had valid alignment,
            // new one is smaller with same alignment so it must be
            // valid as well.
            Layout::from_size_align_unchecked(new_capacity, old_layout.align())
        };

        *base = unsafe { self.inner.alloc.shrink(*base, old_layout, new_layout) }
            .expect("unable to shrink allocated memory");

        Ok(*base)
    }

    /// Stores a `value` of type `T` in the contiguous memory block and returns
    /// a [`SyncContiguousEntryRef<T>`](SyncContiguousEntryRef) pointing
    /// to it.
    ///
    /// Value type argument `T` is used to deduce type size and returned
    /// reference dropping behavior.
    ///
    /// # Panics
    ///
    /// Panics if the collection needs to grow and new capacity exceeds
    /// `isize::MAX` bytes or allocation of additional memory fails.
    ///
    /// # Errors
    ///
    /// A [`LockingError::Poisoned`](crate::error::LockingError::Poisoned) error
    /// is returned when the segment tracker of the container is poisoned.
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
    /// # Panics
    ///
    /// Panics if the collection needs to grow and new capacity exceeds
    /// `isize::MAX` bytes or allocation of additional memory fails.
    ///
    /// # Errors
    ///
    /// A [`LockingError::Poisoned`](crate::error::LockingError::Poisoned) error
    /// is returned when the segment tracker of the container is poisoned.
    pub fn push_persisted<T>(
        &mut self,
        value: T,
    ) -> Result<SyncContiguousEntryRef<T, A>, LockingError> {
        let mut data = ManuallyDrop::new(value);
        let layout = Layout::for_value(&data);
        let pos = &mut *data as *mut T;

        unsafe { self.push_raw_persisted(pos, layout) }
    }

    /// Works same as [`push`](SyncContiguousMemory::push) but takes a `data`
    /// pointer and `layout`.
    ///
    /// Pointer type `T` is used to infer the drop behavior of the returned
    /// reference.
    ///
    /// # Panics
    ///
    /// Panics if the collection needs to grow and new capacity exceeds
    /// `isize::MAX` bytes or allocation of additional memory fails.
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
        let range = loop {
            let base = self.base()?;
            let next = self
                .inner
                .tracker
                .lock_named(LockTarget::SegmentTracker)?
                .take_next(base, layout);
            match next {
                Some(taken) => {
                    let found = taken.offset_base_unwrap(base);
                    unsafe { core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size()) }
                    break taken;
                }
                None => {
                    self.reserve_layout_exact(layout)?;
                }
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
    ///
    /// # Panics
    ///
    /// Panics if the collection needs to grow and new capacity exceeds
    /// `isize::MAX` bytes or allocation of additional memory fails.
    ///
    /// # Safety
    ///
    /// See: [`SyncContiguousMemory::push_raw`]
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
    /// # Safety
    ///
    /// This function isn't unsafe because creating an invalid pointer isn't
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

    /// Clones the allocated memory region into a new `SyncMemoryStorage`.
    ///
    /// This function isn't unsafe, even though it ignores presence of `Copy`
    /// bound on stored data, because it doesn't create any invalid references.
    #[must_use = "unused copied collection"]
    pub fn copy_data(&self) -> Result<Self, LockingError>
    where
        A: Clone,
    {
        let base = self.inner.base.read_named(LockTarget::BaseAddress)?;
        let current_layout = unsafe { base_addr_layout(*base, self.inner.alignment) };
        let result = Self::with_layout_and_alloc(current_layout, self.inner.alloc.clone());
        match *base {
            Some(base) => unsafe {
                core::ptr::copy_nonoverlapping(
                    base.as_ptr() as *const (),
                    result.base().unwrap_unchecked().unwrap_unchecked().as_ptr() as *mut (),
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
    /// to be stored in place of previously stored data, or returns a
    /// [`LockingError::Poisoned`] error if the segment tracker mutex is
    /// poisoned.
    ///
    /// This allows clearing persisted entries created with
    /// [`SyncContiguousMemory::push_persisted`] and
    /// [`SyncContiguousMemory::push_raw_persisted`] methods.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it invalidates any previously returned
    /// references overlapping `region`. Storing data into the container and
    /// then trying to access previously stored data from overlapping regions
    /// will cause undefined behavior.
    pub unsafe fn clear(&mut self) -> Result<(), LockingError> {
        self.inner
            .tracker
            .lock_named(LockTarget::SegmentTracker)?
            .clear();
        Ok(())
    }

    /// Marks the provided `region` of the container as free, allowing new data
    /// to be stored in place of previously stored data, or returns a
    /// [`LockingError::Poisoned`] error if the segment tracker mutex is
    /// poisoned.
    ///
    /// This allows clearing persisted entries created with
    /// [`SyncContiguousMemory::push_persisted`] and
    /// [`SyncContiguousMemory::push_raw_persisted`] methods.
    ///
    /// # Panics
    ///
    /// This function panics in debug mode if the provided region falls outside
    /// of the memory tracked by the segment tracker.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it invalidates any previously returned
    /// references overlapping `region`. Storing data into the container and
    /// then trying to access previously stored data from overlapping regions
    /// will cause undefined behavior.
    pub unsafe fn clear_region(&mut self, region: ByteRange) -> Result<(), LockingError> {
        self.inner
            .tracker
            .lock_named(LockTarget::SegmentTracker)?
            .release(region);
        Ok(())
    }

    /// Forgets this container without dropping it and returns its base address
    /// and [`Layout`], or a [`LockingError::Poisoned`] error if base address
    /// `RwLock` has been poisoned.
    ///
    /// For details on safety see _Safety_ section of
    /// [default implementation](crate::ContiguousMemory::forget).
    pub fn forget(self) -> Result<(BaseAddress, Layout), LockingError> {
        let base = self.base()?;
        let layout = unsafe { base_addr_layout(base, self.inner.alignment) };
        core::mem::forget(self);
        Ok((base, layout))
    }
}

#[cfg(feature = "debug")]
impl<A: ManageMemory> core::fmt::Debug for SyncContiguousMemory<A>
where
    MemoryState<ImplConcurrent, A>: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SyncContiguousMemory")
            .field("inner", &self.inner)
            .finish()
    }
}

impl Default for SyncContiguousMemory {
    fn default() -> Self {
        SyncContiguousMemory::new()
    }
}

impl<A: ManageMemory + Default> Default for SyncContiguousMemory<A> {
    fn default() -> Self {
        SyncContiguousMemory::with_alloc(A::default())
    }
}

impl<A: ManageMemory> Clone for SyncContiguousMemory<A> {
    /// Creates a copy which represents the same memory region as this one.
    ///
    /// If you need to copy the memory region of this container into a new one,
    /// use: [`SyncContiguousMemory::copy_data`]
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}
