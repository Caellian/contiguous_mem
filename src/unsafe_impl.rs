use core::alloc::{Layout, LayoutError};
use core::mem::{size_of, ManuallyDrop};

use crate::error::ContiguousMemoryError;
use crate::sealed::{BaseLocation, MemoryState};
use crate::types::*;
use crate::ByteRange;

/// A memory container for efficient allocation and storage of contiguous data.
///
/// This collection manages a contiguous block of memory, allowing for storage
/// of arbitrary data types while ensuring that stored items are placed
/// adjacently and ensuring they're properly alligned.
///
/// Type argument `Impl` specifies implementation details for the behavior of
/// this struct.
///
/// Note that this structure is a smart abstraction over underlying data,
/// copying it creates a copy which represents the same internal state. If you
/// need to copy the memory region into a new container see:
/// [`ContiguousMemoryStorage::copy_data`]
///
/// # Example
///
/// ```rust
#[doc = include_str!("../examples/unsafe_impl.rs")]
/// ```
#[derive(Clone)]
pub struct UnsafeContiguousMemory {
    inner: MemoryState<crate::ImplUnsafe>,
}

impl UnsafeContiguousMemory {
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
            inner: MemoryState::new_unsafe(base, capacity, alignment),
        })
    }

    /// Creates a new `ContiguousMemory` instance with the provided `layout`.
    pub fn new_for_layout(layout: Layout) -> Self {
        let base = unsafe { allocator::alloc(layout) };
        Self {
            inner: MemoryState::new_unsafe(base, layout.size(), layout.align()),
        }
    }

    /// Returns the base address of the allocated memory.
    pub fn get_base(&self) -> *const () {
        self.inner.base.0 as *const ()
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
    /// let mut storage = UnsafeContiguousMemory::new(0);
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
    /// Shrinking the container is generally performed in place by freeing
    /// tailing memory space, but growing it can move the data in memory to find
    /// a location that can fit it.
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
    ) -> Result<Option<*const ()>, ContiguousMemoryError> {
        let old_capacity = self.inner.capacity;
        if new_capacity == old_capacity {
            return Ok(None);
        }

        self.inner.tracker.resize(new_capacity)?;
        let layout =
            unsafe { Layout::from_size_align_unchecked(old_capacity, self.inner.alignment) };
        let prev_base = self.inner.base;
        self.inner.base =
            BaseLocation(unsafe { allocator::realloc(*prev_base, layout, new_capacity) });
        self.inner.capacity = new_capacity;

        Ok(if self.inner.base.0 != *prev_base {
            Some(self.inner.base.0 as *const ())
        } else {
            None
        })
    }

    /// Reserves exactly `additional` bytes.
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + additional`.
    #[inline]
    pub fn reserve(&mut self, additional: usize) -> Option<*const ()> {
        self.resize(self.get_capacity() + additional)
            .expect("unable to grow the container")
    }

    /// Reserves additional bytes required to store a value with provided
    /// `layout` while keeping it aligned (required padding bytes at the end of
    /// the container will be included).
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + padding + size_of::<V>()`.
    pub fn reserve_layout(&mut self, layout: Layout) -> Option<*const ()> {
        let last = unsafe { self.inner.base.add(self.inner.tracker.len()) };
        let align_offset = last.align_offset(layout.align());
        self.reserve(align_offset + layout.size())
    }

    /// Reserves exactly additional bytes required to store a value of type `V`.
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + size_of::<V>()`.
    #[inline]
    pub fn reserve_type<V>(&mut self) -> Option<*const ()> {
        self.reserve_layout(Layout::new::<V>())
    }

    /// Reserves exactly additional bytes required to store `count` number of
    /// values of type `V`.
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + size_of::<V>() * count`.
    pub fn reserve_type_count<V>(&mut self, count: usize) -> Option<*const ()> {
        let layout = Layout::new::<V>();
        let last = unsafe { self.inner.base.add(self.inner.tracker.len()) };
        let align_offset = last.align_offset(layout.align());
        let inner_padding = unsafe {
            last.add(align_offset + layout.size())
                .align_offset(layout.align())
        };
        self.reserve(align_offset + layout.size() * count + inner_padding * count.saturating_sub(1))
    }

    /// Shrinks the allocated memory to fit the currently stored data and
    /// returns the new capacity.
    pub fn shrink_to_fit(&mut self) -> usize {
        if let Some(new_capacity) = self.inner.tracker.shrink_to_fit() {
            let layout = unsafe {
                Layout::from_size_align_unchecked(self.inner.capacity, self.inner.alignment)
            };
            let prev_base = self.inner.base;
            self.inner.base =
                BaseLocation(unsafe { allocator::realloc(*prev_base, layout, new_capacity) });
            self.inner.capacity = new_capacity;
            new_capacity
        } else {
            self.inner.capacity
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
    /// Memory block can still be grown by calling [`ContiguousMemory::resize`],
    /// but it can't be done automatically as that would invalidate all the
    /// existing pointers without any indication.
    pub fn push<T>(&mut self, value: T) -> Result<*mut T, ContiguousMemoryError> {
        let mut data = ManuallyDrop::new(value);
        let layout = Layout::for_value(&data);
        let pos = &mut *data as *mut T;

        unsafe { self.push_raw(pos, layout) }
    }

    /// Works same as [`push`](ContiguousMemory::push) but takes a pointer and
    /// layout.
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
    ) -> Result<*mut T, ContiguousMemoryError> {
        let base = self.inner.base.0 as usize;
        let addr = match self.inner.tracker.take_next(base, layout) {
            Ok(taken) => {
                let found = (taken.0 + base) as *mut u8;
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
    pub fn assume_stored<T>(&self, position: usize) -> *mut T {
        unsafe { self.inner.base.add(position) as *mut T }
    }

    /// Clones the allocated memory region into a new ContiguousMemoryStorage.
    ///
    /// This function isn't unsafe, even though it ignores presence of `Copy`
    /// bound on stored data, because it doesn't create any pointers.
    #[must_use]
    pub fn copy_data(&self) -> Self {
        let current_layout = self.get_layout();
        let result = Self::new_for_layout(current_layout);
        unsafe {
            core::ptr::copy_nonoverlapping(
                self.get_base(),
                result.get_base() as *mut (),
                current_layout.size(),
            );
        }
        result
    }

    /// Allows freeing a memory range stored at provided `position`.
    ///
    /// Type of the position pointer `T` determines the size of the freed chunk.
    ///
    /// # Safety
    ///
    /// This function is considered unsafe because it can mark a memory range
    /// as free while a valid reference is pointing to it from another place in
    /// code.
    pub unsafe fn free_typed<T>(&mut self, position: *mut T) {
        Self::free(self, position, size_of::<T>())
    }

    /// Allows freeing a memory range stored at provided `position` with the
    /// specified `size`.
    ///
    /// # Safety
    ///
    /// This function is considered unsafe because it can mark a memory range
    /// as free while a valid reference is pointing to it from another place in
    /// code.
    pub unsafe fn free<T>(&mut self, position: *mut T, size: usize) {
        let pos: usize = position.sub(self.inner.base.0 as usize) as usize;
        if let Some(_) = self.inner.tracker.release(ByteRange(pos, pos + size)).ok() {
            core::ptr::drop_in_place(position);
        }
    }

    /// Forgets this container without dropping it and returns its base address
    /// and [`Layout`].
    ///
    /// For details on safety see _Safety_ section of
    /// [default implementation](ContiguousMemoryStorage<ImplDefault>::forget).
    pub fn forget(self) -> (*const (), Layout) {
        let base = self.inner.base.0;
        let layout = self.get_layout();
        core::mem::forget(self);
        (base as *const (), layout)
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
