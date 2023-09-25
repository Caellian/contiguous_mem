use core::alloc::Layout;
use core::mem::{align_of, size_of, ManuallyDrop};
use core::ptr::null_mut;

use crate::error::{MemoryError, NoFreeMemoryError};
use crate::range::ByteRange;
use crate::raw::*;
use crate::types::*;

/// A memory container for efficient allocation and storage of contiguous data.
///
/// This collection manages a contiguous block of memory, allowing for storage
/// of arbitrary data types while ensuring that stored items are placed
/// adjacently and ensuring they're properly alligned.
///
/// Type argument `Impl` specifies implementation details for the behavior of
/// this struct.
///
/// Note that copying this structure creates a copy which represents the same
/// internal state.
/// If you need to copy the memory region into a new container use:
/// [`UnsafeContiguousMemory::copy_data`]
///
/// # Examples
///
/// ```rust
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
        self.inner.capacity
    }

    /// Returns the total size of all stored entries excluding the padding.
    #[inline]
    pub fn size(&self) -> usize {
        self.inner.capacity - self.inner.tracker.count_free()
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
            Layout::from_size_align_unchecked(self.inner.capacity, self.inner.alignment)
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
    /// ```rust
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
    pub fn can_push_t<T>(&self) -> bool {
        let layout = Layout::new::<T>();
        self.inner.tracker.peek_next(layout).is_some()
    }

    /// Returns `true` if the provided `value` can be stored without growing the
    /// container.
    ///
    /// `value` can either be a [`Layout`] or a reference to a `Sized` value.
    pub fn can_push<T>(&self, value: impl HasLayout) -> bool {
        let layout = value.layout();
        self.inner.tracker.peek_next(layout).is_some()
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
            Err(MemoryError::Layout(_)) => panic!("new capacity exceeds `isize::MAX`"),
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
        let old_capacity = self.inner.capacity;
        let new_capacity = core::cmp::max(old_capacity, new_capacity);
        if new_capacity == old_capacity {
            return Ok(None);
        }

        self.inner.tracker.grow(new_capacity);

        let old_layout = self.layout();
        let new_layout = Layout::from_size_align(new_capacity, self.inner.alignment)?;

        let prev_base = self.inner.base.0;
        self.inner.base.0 = unsafe { self.inner.alloc.grow(prev_base, old_layout, new_layout)? };

        self.inner.capacity = new_capacity;

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

    /// Grows the underlying memory by `additional` number of bytes.
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + additional`.
    ///
    /// Make sure to update any previously created pointers.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve(&mut self, additional: usize) -> Option<BasePtr> {
        match self.try_reserve(additional) {
            Ok(it) => it,
            Err(MemoryError::Layout(_)) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("unable to allocate more memory"),
        }
    }

    /// Tries growing the underlying memory by `additional` number of bytes,
    /// returning a [`MemoryError`] error if the new capacity exceeds
    /// `isize::MAX` or the allocator can't allocate required memory.
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + additional`.
    ///
    /// Make sure to update any previously created pointers.
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<Option<BasePtr>, MemoryError> {
        if additional == 0 {
            return Ok(None);
        }

        let old_capacity = self.capacity();
        let new_capacity = old_capacity.saturating_add(additional);

        self.inner.tracker.grow(new_capacity);
        let old_layout = self.layout();
        let new_layout = Layout::from_size_align(new_capacity, self.inner.alignment)?;
        let prev_base = self.base();

        let new_base = unsafe {
            self.inner
                .alloc
                .grow(prev_base, old_layout, new_layout)?
                .unwrap_unchecked()
        };

        self.inner.base.0 = Some(new_base);
        self.inner.capacity = new_capacity;
        Ok(if Some(new_base) != prev_base {
            Some(new_base)
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
    /// Make sure to update any previously created pointers.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve_layout(&mut self, layout: impl HasLayout) -> Option<BasePtr> {
        match self.try_reserve_layout(layout) {
            Ok(it) => it,
            Err(MemoryError::Layout(_)) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("unable to allocate more memory"),
        }
    }

    /// Reserves additional bytes required to store a value with provided
    /// `layout` while keeping it aligned (required padding bytes at the end of
    /// the container will be included).
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + padding + size_of::<V>()`.
    ///
    /// Make sure to update any previously created pointers.
    pub fn try_reserve_layout(
        &mut self,
        layout: impl HasLayout,
    ) -> Result<Option<BasePtr>, MemoryError> {
        let layout = layout.layout();
        match self.base() {
            Some(base) => {
                let last = unsafe { (base.as_ptr() as *mut u8).add(self.inner.tracker.len()) };
                let align_offset = last.align_offset(layout.align());
                self.try_reserve(self.capacity() + align_offset + layout.size())
            }
            None => {
                self.inner.tracker.grow(layout.size());
                let new_layout = Layout::from_size_align(
                    layout.size(),
                    core::cmp::max(self.inner.alignment, layout.align()),
                )?;

                let new_base = unsafe { self.inner.alloc.allocate(new_layout)?.unwrap_unchecked() };

                self.inner.base.0 = Some(new_base);
                self.inner.capacity = layout.size();
                Ok(Some(new_base))
            }
        }
    }

    /// Shrinks the capacity with a lower bound and returns the base pointer.
    ///
    /// # Panics
    ///
    /// Panics if the allocator wasn't able to shrink the allocated memory
    /// region.
    pub fn shrink_to(&mut self, new_capacity: usize) -> BaseAddress {
        let new_capacity = core::cmp::max(self.inner.tracker.min_len(), new_capacity);
        self.inner.tracker.shrink(new_capacity);
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

        let new_base = unsafe {
            self.inner
                .alloc
                .shrink(prev_base, self.layout(), new_layout)
        }
        .expect("unable to shrink the container");

        self.inner.base.0 = new_base;
        self.inner.capacity = new_capacity;

        new_base
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
        let new_base = unsafe { self.inner.alloc.shrink(prev_base, old_layout, new_layout) }
            .expect("unable to shrink allocated memory");
        self.inner.base.0 = new_base;
        self.inner.capacity = new_capacity;
        new_base
    }

    /// Stores a `value` of type `T` in the contiguous memory block and returns
    /// a reference or a pointer pointing to it, or a [`NoFreeMemoryError`]
    /// error if the container couldn't store the provided data with current
    /// capacity.
    ///
    /// Value type argument `T` is used to infer type size.
    ///
    /// Unsafe implementation requres manually calling
    /// [`UnsafeContiguousMemory::resize`] as growing the capacity almost always
    /// causes a reallocation which would invalidate all the existing pointers
    /// without any indication.
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
            Ok(taken) => {
                let found = taken.offset_base_unwrap(base);
                unsafe {
                    core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                }
                found
            }
            Err(_) => return Err(NoFreeMemoryError),
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
    /// ```rust
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

    /// Clones the allocated memory region into a new UnsafeContiguousMemory.
    ///
    /// This function isn't unsafe, even though it ignores presence of `Copy`
    /// bound on stored data, because it doesn't create any pointers.
    #[must_use]
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
        match self.inner.base.0 {
            Some(base) => {
                let pos: usize = position.sub(base.as_ptr() as *const u8 as usize) as usize;
                self.inner.tracker.release(ByteRange(pos, pos + size));
                core::ptr::drop_in_place(position);
            }
            None => {}
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
    pub unsafe fn free_typed<T>(&mut self, position: *mut T) {
        Self::free(self, position, size_of::<T>())
    }

    /// Marks the entire contents of the container as free, allowing new data
    /// to be stored in place of previously stored data.
    ///
    /// This function isn't unsafe because responsibility for validity of
    /// underlying data must be ensured when pointers are dereferenced.
    pub fn clear(&mut self) {
        self.inner.tracker.clear();
    }

    /// Marks the provided `region` of the container as free, allowing new data
    /// to be stored in place of previously stored data.
    ///
    /// # Panics
    ///
    /// This function panics in debug mode if the provided region falls outside
    /// of the memory tracked by the allocation tracker.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it invalidates any previously returned
    /// pointers overlapping `region`. Storing data into the container and
    /// then trying to access previously stored data from overlapping regions
    /// will cause undefined behavior.
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
impl core::fmt::Debug for UnsafeContiguousMemory
where
    MemoryState<ImplUnsafe>: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("UnsafeContiguousMemory")
            .field("inner", &self.inner)
            .finish()
    }
}

impl<A: ManageMemory + Clone> Clone for UnsafeContiguousMemory<A> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}
