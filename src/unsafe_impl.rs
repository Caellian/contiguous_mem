use core::alloc::Layout;
use core::mem::{align_of, size_of, ManuallyDrop};
use core::ptr::null_mut;

use crate::common::*;
use crate::error::{MemoryError, NoFreeMemoryError};
use crate::memory::{DefaultMemoryManager, ManageMemory};
use crate::range::ByteRange;
use crate::raw::*;

/// An unsafe version of [`ContiguousMemory`](crate::ContiguousMemory), refer to
/// it for usage examples.
///
/// # Examples
///
/// ```
#[doc = include_str!("../examples/unsafe_impl.rs")]
/// ```
pub struct UnsafeContiguousMemory<A: ManageMemory = DefaultMemoryManager> {
    inner: MemoryState<crate::ImplUnsafe, A>,
}

impl UnsafeContiguousMemory {
    /// Creates a new zero-sized `ContiguousMemory` instance aligned with
    /// alignment of `usize`.
    pub fn new() -> Self {
        Self {
            inner: unsafe {
                MemoryState::new_unsafe(Layout::from_size_align_unchecked(0, align_of::<usize>()))
                    .expect("unable to create an empty container")
            },
        }
    }

    /// Creates a new `ContiguousMemory` instance with the specified `capacity`,
    /// aligned with alignment of `usize`.
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
            Layout::from_size_align_unchecked(capacity, align_of::<usize>())
        })
    }

    /// Creates a new `UnsafeContiguousMemory` instance with capacity and
    /// alignment of the provided `layout`.
    ///
    /// # Panics
    ///
    /// Panics if capacity exceeds `isize::MAX` bytes or the allocator can't
    /// provide required amount of memory.
    pub fn with_layout(layout: Layout) -> Self {
        Self {
            inner: match MemoryState::new_unsafe(layout) {
                Ok(it) => it,
                Err(_) => panic!("unable to create a container with layout: {:?}", layout),
            },
        }
    }
}

impl<A: ManageMemory> UnsafeContiguousMemory<A> {
    /// Creates a new zero-sized `ContiguousMemory` instance aligned with
    /// alignment of `usize` that uses the specified allocator.
    pub fn with_alloc(alloc: A) -> Self {
        unsafe {
            Self {
                inner: MemoryState::new_unsafe_with_alloc(
                    Layout::from_size_align_unchecked(0, align_of::<usize>()),
                    alloc,
                )
                .expect("unable to create an empty container"),
            }
        }
    }

    /// Creates a new `ContiguousMemory` instance with the specified `capacity`,
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

    /// Creates a new `ContiguousMemory` instance with capacity and alignment of
    /// the provided `layout`.
    ///
    /// This method will panic if there's no more memory available.
    pub fn with_layout_and_alloc(layout: Layout, alloc: A) -> Self {
        Self {
            inner: match MemoryState::new_unsafe_with_alloc(layout, alloc) {
                Ok(it) => it,
                Err(_) => unreachable!("unable to create a container with layout: {:?}", layout),
            },
        }
    }

    /// Returns the base address of the allocated memory.
    #[inline]
    pub fn base(&self) -> BaseAddress {
        self.inner.base.0
    }

    /// Returns a pointer to the base address of the allocated memory or `null`
    /// if the container didn't allocate.
    pub fn base_ptr(&self) -> *const u8 {
        match self.base() {
            Some(it) => it.as_ptr() as *const u8,
            None => core::ptr::null(),
        }
    }

    /// Returns the current capacity of the memory container.
    ///
    /// The capacity represents the size of the memory block that has been
    /// allocated for storing data. It may be larger than the amount of data
    /// currently stored within the container.
    #[inline]
    pub fn capacity(&self) -> usize {
        base_addr_capacity(self.base())
    }

    /// Returns the total size of all stored entries excluding the padding.
    #[inline]
    pub fn size(&self) -> usize {
        self.capacity() - self.inner.tracker.count_free()
    }

    /// Returns the alignment of the memory container.
    #[inline]
    pub fn align(&self) -> usize {
        self.inner.alignment
    }

    /// Returns the layout of the memory region containing stored data.
    #[inline]
    pub fn layout(&self) -> Layout {
        unsafe {
            // SAFETY: Constructor would panic if Layout was invalid.
            Layout::from_size_align_unchecked(self.capacity(), self.align())
        }
    }

    /// Returns `true` if the provided value can be stored without growing the
    /// container.
    ///
    /// It's usually clearer to try storing the value directly and then handle
    /// the case where it wasn't stored through error matching.
    ///
    /// # Examples
    ///
    /// ```
    /// # use contiguous_mem::UnsafeContiguousMemory;
    /// # use core::mem::size_of_val;
    /// let mut storage = UnsafeContiguousMemory::new();
    /// let value = [2, 4, 8, 16];
    ///
    /// # assert_eq!(storage.can_push_t::<Vec<i32>>(), false);
    /// if !storage.can_push_t::<Vec<i32>>() {
    ///     storage.grow_to(storage.capacity() + size_of_val(&value));
    ///     // update pointers...
    /// }
    ///
    /// let stored_value =
    ///   storage.push(value).expect("unable to store after growing the container");
    /// ```
    #[inline]
    pub fn can_push_t<T>(&self) -> bool {
        self.can_push(Layout::new::<T>())
    }

    /// Returns `true` if the provided `value` can be stored without growing the
    /// container.
    ///
    /// `value` can either be a [`Layout`] or a reference to a `Sized` value.
    #[inline]
    pub fn can_push(&self, value: impl HasLayout) -> bool {
        self.inner
            .tracker
            .can_store(self.inner.base.0, value.as_layout())
    }

    /// Grows the memory container to the specified `new_capacity`, optionally
    /// returning the new base address and size of the underlying memory.
    ///
    /// If the base address of the memory block stays the same the returned
    /// value is `None`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` or the allocator
    /// operation fails.
    pub fn grow_to(&mut self, new_capacity: usize) -> Option<BasePtr> {
        match self.try_grow_to(new_capacity) {
            Ok(it) => it,
            Err(MemoryError::TooLarge) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("allocator error"),
        }
    }

    /// Tries resizing the memory container to the specified `new_capacity`,
    /// optionally returning the new base address and size of the underlying
    /// memory, or a [`MemoryError`] if the new capacity exceeds `isize::MAX` or
    /// the allocator can't allocate required memory.
    ///
    /// If the base address of the memory block stays the same the returned
    /// value is `None`.
    ///
    /// Make sure to update any previously created pointers.
    pub fn try_grow_to(&mut self, new_capacity: usize) -> Result<Option<BasePtr>, MemoryError> {
        let old_capacity = self.capacity();
        let new_capacity = self.inner.tracker.grow(new_capacity);
        if new_capacity == old_capacity {
            return Ok(None);
        };

        let old_layout = self.layout();
        let new_layout = Layout::from_size_align(new_capacity, self.inner.alignment)
            .map_err(|_| MemoryError::TooLarge)?;

        let prev_base = self.inner.base.0;
        self.inner.base.0 = unsafe { self.inner.alloc.grow(prev_base, old_layout, new_layout)? };

        Ok(if self.inner.base.0 != prev_base {
            Some(unsafe {
                // SAFETY: new_capacity must be > 0, because it's max of
                // old_capacity and passed argument, if both are 0 we return
                // early
                self.inner.base.0.unwrap_unchecked()
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
    ) -> Result<Option<BasePtr>, MemoryError> {
        let (capacity, last_offset, largest_free, tailing_free) = {
            let tracker = &self.inner.tracker;
            (
                tracker.size(),
                tracker.last_offset(),
                tracker.largest_free_range(),
                tracker.tailing_free_bytes(),
            )
        };
        let base_pos = self.base_ptr() as usize;

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
    /// After calling this function, new capacity will be greater than:
    /// `self.size() + capacity`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve(&mut self, capacity: usize) -> Option<BasePtr> {
        match self.try_reserve(capacity) {
            Ok(it) => it,
            Err(MemoryError::TooLarge) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("unable to allocate more memory"),
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
    ///
    /// After calling this function, new capacity will be greater than:
    /// `self.size() + capacity`.
    pub fn try_reserve(&mut self, capacity: usize) -> Result<Option<BasePtr>, MemoryError> {
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
    /// After calling this function, new capacity will be equal to:
    /// `self.size() + capacity`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve_exact(&mut self, capacity: usize) -> Option<BasePtr> {
        match self.try_reserve_exact(capacity) {
            Ok(it) => it,
            Err(MemoryError::TooLarge) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("unable to allocate more memory"),
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
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.size() + capacity`.
    pub fn try_reserve_exact(&mut self, capacity: usize) -> Result<Option<BasePtr>, MemoryError> {
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
    /// After calling this function, new capacity will be greater than:
    /// `self.size() + padding + size_of::<V>()`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve_layout(&mut self, layout: impl HasLayout) -> Option<BasePtr> {
        match self.try_reserve_layout(layout) {
            Ok(it) => it,
            Err(MemoryError::TooLarge) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("unable to allocate more memory"),
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
    ///
    /// After calling this function, new capacity will be greater than:
    /// `self.size() + padding + size_of::<V>()`.
    pub fn try_reserve_layout(
        &mut self,
        layout: impl HasLayout,
    ) -> Result<Option<BasePtr>, MemoryError> {
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
    /// After calling this function, new capacity will be equal to:
    /// `self.size() + padding + size_of::<V>()`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve_layout_exact(&mut self, layout: impl HasLayout) -> Option<BasePtr> {
        match self.try_reserve_layout_exact(layout) {
            Ok(it) => it,
            Err(MemoryError::TooLarge) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("unable to allocate more memory"),
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
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.size() + padding + layout.size()`.
    pub fn try_reserve_layout_exact(
        &mut self,
        layout: impl HasLayout,
    ) -> Result<Option<BasePtr>, MemoryError> {
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
    pub fn shrink_to(&mut self, new_capacity: usize) -> BaseAddress {
        let new_capacity = self.inner.tracker.shrink(new_capacity);

        let prev_base = self.inner.base.0;

        let old_layout = self.layout();
        if new_capacity == old_layout.size() {
            return prev_base;
        }
        let new_layout = unsafe {
            // SAFETY: Previous layout was valid and had valid alignment,
            // new one is smaller with same alignment so it must be
            // valid as well.
            Layout::from_size_align_unchecked(new_capacity, old_layout.align())
        };

        self.inner.base.0 = unsafe {
            self.inner
                .alloc
                .shrink(prev_base, self.layout(), new_layout)
        }
        .expect("unable to shrink the container");

        self.inner.base.0
    }

    /// Shrinks the allocated memory to fit the currently stored data and
    /// returns the new capacity.
    pub fn shrink_to_fit(&mut self) -> BaseAddress {
        let prev_base = self.inner.base.0;
        let new_capacity = match self.inner.tracker.shrink_to_fit() {
            Some(it) => it,
            None => return prev_base,
        };
        let old_layout = self.layout();
        let new_layout = unsafe {
            // SAFETY: Previous layout was valid and had valid alignment,
            // new one is smaller with same alignment so it must be
            // valid as well.
            Layout::from_size_align_unchecked(new_capacity, old_layout.align())
        };
        let prev_base = self.inner.base.0;
        self.inner.base.0 = unsafe { self.inner.alloc.shrink(prev_base, old_layout, new_layout) }
            .expect("unable to shrink allocated memory");

        self.inner.base.0
    }

    /// Stores a `value` of type `T` in the contiguous memory block and returns
    /// a reference or a pointer pointing to it, or a [`NoFreeMemoryError`]
    /// error if the container couldn't store the provided data with current
    /// capacity.
    ///
    /// Value type argument `T` is used to infer type size.
    ///
    /// Unsafe implementation requres manually calling
    /// [`UnsafeContiguousMemory::grow_to`] as growing the capacity almost
    /// always causes a reallocation which would invalidate all the existing
    /// pointers without any indication.
    pub fn push<T>(&mut self, value: T) -> Result<*mut T, NoFreeMemoryError> {
        let mut data = ManuallyDrop::new(value);
        let layout = Layout::for_value(&data);
        let pos = &mut *data as *mut T;

        unsafe { self.push_raw(pos, layout) }
    }

    /// Works same as [`push`](UnsafeContiguousMemory::push) but takes a `data`
    /// pointer and `layout`.
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
    ) -> Result<*mut T, NoFreeMemoryError> {
        let base = self.inner.base.0;
        let addr = match self.inner.tracker.take_next(base, layout) {
            Some(taken) => {
                let found = taken.offset_base_unwrap(base);
                unsafe {
                    core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                }
                found
            }
            None => return Err(NoFreeMemoryError),
        };

        Ok(addr as *mut T)
    }

    /// Assumes value is stored at the provided _relative_ `position` in
    /// managed memory and returns a pointer or a reference to it.
    ///
    /// If the container capacity is 0, a null pointer will be returned instead.
    ///
    /// # Safety
    ///
    /// This function isn't unsafe because creating an invalid pointer isn't
    /// considered unsafe. Responsibility for guaranteeing safety falls on
    /// code that's dereferencing the pointer.
    ///
    /// # Examples
    /// ```
    /// # use contiguous_mem::UnsafeContiguousMemory;
    /// let mut storage = UnsafeContiguousMemory::with_capacity(128);
    /// let initial_position = storage.push(278u32).unwrap();
    ///
    /// let base_addr = storage.base_ptr();
    /// storage.grow_to(512);
    ///
    /// let new_position: *mut u32 = storage.assume_stored(
    ///     initial_position as usize - base_addr as usize
    /// );
    /// unsafe {
    ///     assert_eq!(*new_position, 278u32);
    /// }
    /// ```
    pub fn assume_stored<T>(&self, position: usize) -> *mut T {
        match self.inner.base.0 {
            Some(base) => unsafe { (base.as_ptr() as *mut u8).add(position) as *mut T },
            None => null_mut(),
        }
    }

    /// Clones the allocated memory region into a new `UnsafeContiguousMemory`.
    ///
    /// This function isn't unsafe, even though it ignores presence of `Copy`
    /// bound on stored data, because it doesn't create any pointers.
    #[must_use = "unused copied collection"]
    pub fn copy_data(&self) -> Self
    where
        A: Clone,
    {
        let current_layout = self.layout();
        let result = Self::with_layout_and_alloc(current_layout, self.inner.alloc.clone());
        match self.base() {
            Some(base) => unsafe {
                core::ptr::copy_nonoverlapping(
                    base.as_ptr() as *const (),
                    result.base().unwrap_unchecked().as_ptr() as *mut (),
                    current_layout.size(),
                );
            },
            None => {
                // empty structure; nothing to copy
            }
        }
        result
    }

    /// Allows freeing a memory range stored at provided `position` with the
    /// specified `size`.
    ///
    /// If underlying memory isn't allocated, this function is a no-op.
    ///
    /// # Safety
    ///
    /// This function is considered unsafe because it can mark a memory range
    /// as free while a dereferenced pointer is pointing to it from another
    /// place in code.
    pub unsafe fn free<T>(&mut self, position: *mut T, size: usize) {
        if let Some(base) = self.inner.base.0 {
            let pos: usize = position.sub(base.as_ptr() as *const u8 as usize) as usize;
            self.inner.tracker.release(ByteRange(pos, pos + size));
            core::ptr::drop_in_place(position);
        }
    }

    /// Allows freeing a memory region dedicated to pointed-to type `T` stored
    /// at provided `position`.
    ///
    /// Type `T` determines the size of the freed memory region.
    ///
    /// If underlying memory isn't allocated, this function is a no-op.
    ///
    /// # Safety
    ///
    /// See: [`UnsafeContiguousMemory::free`]
    #[inline]
    pub unsafe fn free_typed<T>(&mut self, position: *mut T) {
        self.free(position, size_of::<T>())
    }

    /// Marks the entire contents of the container as free, allowing new data
    /// to be stored in place of previously stored data.
    ///
    /// This function isn't unsafe because responsibility for validity of
    /// underlying data must be ensured when pointers are dereferenced.
    #[inline]
    pub fn clear(&mut self) {
        self.inner.tracker.clear();
    }

    /// Marks the provided `region` of the container as free, allowing new data
    /// to be stored in place of previously stored data.
    ///
    /// # Panics
    ///
    /// This function panics in debug mode if the provided region falls outside
    /// of the memory tracked by the segment tracker.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it invalidates any previously returned
    /// pointers overlapping `region`. Storing data into the container and
    /// then trying to access previously stored data from overlapping regions
    /// will cause undefined behavior.
    #[inline]
    pub unsafe fn clear_region(&mut self, region: ByteRange) {
        self.inner.tracker.release(region);
    }

    /// Forgets this container without dropping it and returns its base address
    /// and [`Layout`].
    ///
    /// For details on safety see _Safety_ section of
    /// [default implementation](crate::ContiguousMemory::forget).
    pub fn forget(self) -> (BaseAddress, Layout) {
        let base = self.inner.base.0;
        let layout = self.layout();
        core::mem::forget(self);
        (base, layout)
    }
}

#[cfg(feature = "debug")]
impl<A: ManageMemory> core::fmt::Debug for UnsafeContiguousMemory<A>
where
    MemoryState<crate::common::ImplUnsafe, A>: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("UnsafeContiguousMemory")
            .field("inner", &self.inner)
            .finish()
    }
}

impl Default for UnsafeContiguousMemory {
    fn default() -> Self {
        UnsafeContiguousMemory::new()
    }
}

impl<A: ManageMemory + Default> Default for UnsafeContiguousMemory<A> {
    fn default() -> Self {
        UnsafeContiguousMemory::with_alloc(A::default())
    }
}

impl<A: ManageMemory + Clone> Clone for UnsafeContiguousMemory<A> {
    /// Creates a copy which represents the same memory region as this one.
    ///
    /// If you need to copy the memory region of this container into a new one,
    /// use: [`UnsafeContiguousMemory::copy_data`]
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}
