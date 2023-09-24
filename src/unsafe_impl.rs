use core::alloc::Layout;
use core::mem::{align_of, size_of, ManuallyDrop};
use core::ptr::null_mut;

use crate::error::ContiguousMemoryError;
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
/// # Example
///
/// ```rust
#[doc = include_str!("../examples/unsafe_impl.rs")]
/// ```
pub struct UnsafeContiguousMemory<A: MemoryManager = DefaultMemoryManager> {
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
    pub fn new_with_capacity(capacity: usize) -> Self {
        if !is_layout_valid(capacity, align_of::<usize>()) {
            panic!(
                "capacity too large; max: {}",
                isize::MAX as usize - (align_of::<usize>() - 1)
            )
        }
        Self::new_with_layout(unsafe {
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
    pub fn new_with_layout(layout: Layout) -> Self {
        Self {
            inner: match MemoryState::new_unsafe(layout) {
                Ok(it) => it,
                Err(_) => unreachable!("unable to create a container with layout: {:?}", layout),
            },
        }
    }
}

impl<A: MemoryManager> UnsafeContiguousMemory<A> {
    /// Creates a new zero-sized `ContiguousMemory` instance aligned with
    /// alignment of `usize`.
    pub fn new_with_alloc(alloc: A) -> Self {
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

    /// Creates a new `ContiguousMemory` instance with capacity and alignment of
    /// the provided `layout`.
    ///
    /// This method will panic if there's no more memory available.
    pub fn new_with_layout_and_alloc(layout: Layout, alloc: A) -> Self {
        Self {
            inner: match MemoryState::new_unsafe_with_alloc(layout, alloc) {
                Ok(it) => it,
                Err(_) => unreachable!("unable to create a container with layout: {:?}", layout),
            },
        }
    }

    /// Returns the base address of the allocated memory.
    pub fn get_base(&self) -> BaseAddress {
        self.inner.base.0
    }

    /// Returns the current capacity of the memory container.
    ///
    /// The capacity represents the size of the memory block that has been
    /// allocated for storing data. It may be larger than the amount of data
    /// currently stored within the container.
    pub fn get_capacity(&self) -> usize {
        self.inner.capacity
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
            Layout::from_size_align_unchecked(self.inner.capacity, self.inner.alignment)
        }
    }

    /// Returns `true` if the provided value can be stored without growing the
    /// container.
    ///
    /// It's usually clearer to try storing the value directly and then handle
    /// the case where it wasn't stored through error matching.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use contiguous_mem::UnsafeContiguousMemory;
    /// # use core::mem::size_of_val;
    /// let mut storage = UnsafeContiguousMemory::new();
    /// let value = [2, 4, 8, 16];
    ///
    /// # assert_eq!(storage.can_push::<Vec<i32>>(), false);
    /// if !storage.can_push::<Vec<i32>>() {
    ///     storage.resize(storage.get_capacity() + size_of_val(&value));
    ///
    ///     // ...update old pointers...
    /// }
    ///
    /// let stored_value =
    ///   storage.push(value).expect("unable to store after growing the container");
    /// ```
    pub fn can_push<T>(&self) -> bool {
        let layout = Layout::new::<T>();
        self.inner.tracker.peek_next(layout).is_some()
    }

    /// Returns `true` if the provided `value` can be stored without growing the
    /// container.
    pub fn can_push_value<T>(&self, value: &T) -> bool {
        let layout = Layout::for_value(value);
        self.inner.tracker.peek_next(layout).is_some()
    }

    /// Returns `true` if the provided `layout` can be stored without growing
    /// the container.
    pub fn can_push_layout(&self, layout: Layout) -> bool {
        self.inner.tracker.peek_next(layout).is_some()
    }

    /// Resizes the memory container to the specified `new_capacity`, optionally
    /// returning the new base address of the stored items - if `None` is
    /// returned the base address of the memory block is the same.
    ///
    /// Make sure to update any previously created pointers if the result of
    /// this function is `Ok(Some(new_base_address))`.
    ///
    /// # Errors
    ///
    /// [`ContiguousMemoryError::Unshrinkable`] error is returned when
    /// attempting to shrink the memory container, but previously stored data
    /// prevents the container from being shrunk to the desired capacity.
    pub fn resize(
        &mut self,
        new_capacity: usize,
    ) -> Result<Option<BaseAddress>, ContiguousMemoryError> {
        let old_capacity = self.inner.capacity;
        if new_capacity == old_capacity {
            return Ok(None);
        }

        self.inner.tracker.resize(new_capacity)?;
        let old_layout = self.get_layout();
        let new_layout = Layout::from_size_align(new_capacity, self.inner.alignment)?;
        let prev_base = self.inner.base.0;
        self.inner.base.0 = unsafe {
            if new_capacity > old_capacity {
                self.inner.alloc.grow(prev_base, old_layout, new_layout)?
            } else {
                self.inner.alloc.shrink(prev_base, old_layout, new_layout)?
            }
        };
        self.inner.capacity = new_capacity;

        Ok(if self.inner.base.0 != prev_base {
            Some(self.inner.base.0)
        } else {
            None
        })
    }

    /// Reserves exactly `additional` bytes.
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + additional`.
    #[inline]
    pub fn reserve(&mut self, additional: usize) -> Option<BaseAddress> {
        self.resize(self.get_capacity() + additional)
            .expect("unable to grow the container")
    }

    /// Reserves additional bytes required to store a value with provided
    /// `layout` while keeping it aligned (required padding bytes at the end of
    /// the container will be included).
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + padding + size_of::<V>()`.
    pub fn reserve_layout(&mut self, layout: Layout) -> Option<BaseAddress> {
        match self.get_base() {
            Some(base) => {
                let last = unsafe { (base.as_ptr() as *mut u8).add(self.inner.tracker.len()) };
                let align_offset = last.align_offset(layout.align());
                self.reserve(align_offset + layout.size())
            }
            None => self.reserve(layout.size()),
        }
    }

    /// Shrinks the allocated memory to fit the currently stored data and
    /// returns the new capacity.
    pub fn shrink_to_fit(&mut self) -> BaseAddress {
        if let Some(new_capacity) = self.inner.tracker.shrink_to_fit() {
            let old_layout = self.get_layout();
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
        } else {
            self.get_base()
        }
    }

    /// Stores a `value` of type `T` in the contiguous memory block and returns
    /// a reference or a pointer pointing to it.
    ///
    /// Value type argument `T` is used to deduce type size and returned
    /// reference dropping behavior.
    ///
    /// # Errors
    ///
    /// Unsafe implementation returns a [`ContiguousMemoryError::NoStorageLeft`]
    /// indicating that the container couldn't store the provided data with
    /// current size.
    ///
    /// Memory block can still be grown by calling
    /// [`UnsafeContiguousMemory::resize`], but it can't be done automatically
    /// as that would invalidate all the existing pointers without any
    /// indication.
    pub fn push<T>(&mut self, value: T) -> Result<*mut T, ContiguousMemoryError> {
        let mut data = ManuallyDrop::new(value);
        let layout = Layout::for_value(&data);
        let pos = &mut *data as *mut T;

        unsafe { self.push_raw(pos, layout) }
    }

    /// Works same as [`push`](UnsafeContiguousMemory::push) but takes a pointer
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
    ) -> Result<*mut T, ContiguousMemoryError> {
        let base = self.inner.base.0;
        let addr = match self.inner.tracker.take_next(base, layout) {
            Ok(taken) => {
                let found = taken.offset_base_unwrap(base);
                unsafe {
                    core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                }
                found
            }
            Err(other) => return Err(other),
        };

        Ok(addr as *mut T)
    }

    /// Assumes value is stored at the provided _relative_ `position` in
    /// managed memory and returns a pointer or a reference to it.
    ///
    /// If the container capacity is 0, a null pointer will be returned instead.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use contiguous_mem::UnsafeContiguousMemory;
    /// let mut storage = UnsafeContiguousMemory::new_with_capacity(128);
    /// let initial_position = storage.push(278u32).unwrap();
    ///
    /// // ...other code...
    ///
    /// let base_addr = storage.get_base().unwrap().as_ptr() as *const u8;
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
        let current_layout = self.get_layout();
        let result = Self::new_with_layout_and_alloc(current_layout, self.inner.alloc.clone());
        match self.get_base() {
            Some(base) => unsafe {
                core::ptr::copy_nonoverlapping(
                    base.as_ptr() as *const (),
                    result.get_base().unwrap_unchecked().as_ptr() as *mut (),
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
                if let Some(_) = self.inner.tracker.release(ByteRange(pos, pos + size)).ok() {
                    core::ptr::drop_in_place(position);
                }
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
    /// # Errors
    ///
    /// This function returns a [`ContiguousMemoryError::NotContained`] error if
    /// the provided region falls outside of the memory tracked by the
    /// allocation tracker.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it doesn't invalidate any previously
    /// returned references overlapping `region`. Storing data into the
    /// container and then trying to access previously stored data from
    /// overlapping regions will cause undefined behavior.
    pub unsafe fn clear_region(&mut self, region: ByteRange) -> Result<(), ContiguousMemoryError> {
        self.inner.tracker.release(region)
    }

    /// Forgets this container without dropping it and returns its base address
    /// and [`Layout`].
    ///
    /// For details on safety see _Safety_ section of
    /// [default implementation](crate::ContiguousMemory::forget).
    pub fn forget(self) -> (BaseAddress, Layout) {
        let base = self.inner.base.0;
        let layout = self.get_layout();
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

impl<A: MemoryManager + Clone> Clone for UnsafeContiguousMemory<A> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}
