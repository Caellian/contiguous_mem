#![allow(incomplete_features)]
#![cfg_attr(feature = "no_std", no_std)]
#![cfg_attr(feature = "ptr_metadata", feature(ptr_metadata, unsize))]
#![cfg_attr(feature = "error_in_core", feature(error_in_core))]
#![cfg_attr(feature = "allocator_api", feature(allocator_api))]
#![cfg_attr(doc, feature(doc_auto_cfg))]
#![warn(missing_docs)]
#![doc = include_str!("../doc/crate.md")]

#[cfg(feature = "no_std")]
extern crate alloc;

mod common;
pub mod error;
pub mod range;
mod raw;
pub mod refs;
pub mod tracker;
mod types;

#[cfg(feature = "sync")]
mod sync;
#[cfg(feature = "sync")]
pub use sync::SyncContiguousMemory;

#[cfg(feature = "unsafe")]
mod unsafe_impl;
#[cfg(feature = "unsafe")]
pub use unsafe_impl::UnsafeContiguousMemory;

// Re-exports

/// Memory allocation and management primitives.
pub mod memory {
    pub use crate::raw::{BaseAddress, BasePtr, DefaultMemoryManager, MemoryManager};
}
pub use memory::*;
pub use refs::{CERef, ContiguousEntryRef};
#[cfg(feature = "sync")]
pub use refs::{SCERef, SyncContiguousEntryRef};
#[cfg(feature = "ptr_metadata")]
pub use types::static_metadata;

use core::cell::Cell;
use core::marker::PhantomData;
use core::mem::align_of;
use core::{
    alloc::Layout,
    mem::{size_of, ManuallyDrop},
    ops::Deref,
};

use common::*;
use error::ContiguousMemoryError;
use range::ByteRange;
use raw::*;
use refs::sealed::{BorrowState, ReferenceState};
use types::*;

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
/// [`ContiguousMemory::copy_data`]
///
/// # Example
///
/// ```rust
#[doc = include_str!("../examples/default_impl.rs")]
/// ```
#[derive(Clone)]
pub struct ContiguousMemory<A: MemoryManager = DefaultMemoryManager> {
    inner: Rc<MemoryState<ImplDefault, A>>,
}

impl ContiguousMemory {
    /// Creates a new zero-sized `ContiguousMemory` instance aligned with
    /// alignment of `usize`.
    pub fn new() -> Self {
        Self {
            inner: unsafe {
                MemoryState::new(Layout::from_size_align_unchecked(0, align_of::<usize>()))
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

    /// Creates a new `ContiguousMemory` instance with capacity and alignment of
    /// the provided `layout`.
    ///
    /// # Panics
    ///
    /// Panics if capacity exceeds `isize::MAX` bytes or the allocator can't
    /// provide required amount of memory.
    pub fn new_with_layout(layout: Layout) -> Self {
        Self {
            inner: match MemoryState::new(layout) {
                Ok(it) => it,
                Err(_) => unreachable!("unable to create a container with layout: {:?}", layout),
            },
        }
    }
}

impl<A: MemoryManager> ContiguousMemory<A> {
    /// Creates a new zero-sized `ContiguousMemory` instance aligned with
    /// alignment of `usize`.
    pub fn new_with_alloc(alloc: A) -> Self {
        unsafe {
            Self {
                inner: MemoryState::new_with_alloc(
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
            inner: match MemoryState::new_with_alloc(layout, alloc) {
                Ok(it) => it,
                Err(_) => unreachable!("unable to create a container with layout: {:?}", layout),
            },
        }
    }

    /// Returns the base address of the allocated memory.
    #[inline]
    pub fn get_base(&self) -> BaseAddress {
        self.inner.base.get()
    }

    /// Returns the current capacity of the memory container.
    ///
    /// The capacity represents the size of the memory block that has been
    /// allocated for storing data. It may be larger than the amount of data
    /// currently stored within the container.
    #[inline]
    pub fn get_capacity(&self) -> usize {
        self.inner.capacity.get()
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
            Layout::from_size_align_unchecked(self.inner.capacity.get(), self.inner.alignment)
        }
    }

    /// Returns `true` if provided generic type `T` can be stored without
    /// growing the container.
    pub fn can_push<T>(&self) -> bool {
        let layout = Layout::new::<T>();
        let tracker = self.inner.tracker.borrow();
        tracker.peek_next(layout).is_some()
    }

    /// Returns `true` if the provided `value` can be stored without growing the
    /// container.
    pub fn can_push_value<T>(&self, value: &T) -> bool {
        let layout = Layout::for_value(value);
        let tracker = self.inner.tracker.borrow();
        tracker.peek_next(layout).is_some()
    }

    /// Returns `true` if the provided `layout` can be stored without growing
    /// the container.
    pub fn can_push_layout(&self, layout: Layout) -> bool {
        let tracker = self.inner.tracker.borrow();
        tracker.peek_next(layout).is_some()
    }

    /// Resizes the memory container to the specified `new_capacity`, optionally
    /// returning the new base address and size of the stored items.
    ///
    /// If the base address of the memory block is the same the returned value
    /// is `None`. If `new_capacity` is 0, the retuned pointer will be an
    /// invalid pointer with container alignment.
    ///
    /// # Errors
    ///
    /// [`ContiguousMemoryError::Unshrinkable`] error is returned when
    /// attempting to shrink the memory container, but previously stored data
    /// prevents the container from being shrunk to the desired capacity.
    ///
    /// [`ContiguousMemoryError::Layout`] error is returned when attempting to
    /// grow the container to a capacity larger than addressable by the target.
    ///
    /// [`ContiguousMemoryError::MemoryManager`] error is returned when
    /// the allocator can't allocate a memory region with `new_capacity`
    /// because it either exceeds `isize::MAX` or allocator is out of memory.
    pub fn resize(
        &mut self,
        new_capacity: usize,
    ) -> Result<Option<BasePtr>, ContiguousMemoryError> {
        let old_capacity = self.get_capacity();
        if new_capacity == old_capacity {
            return Ok(None);
        }

        self.inner.tracker.borrow_mut().resize(new_capacity)?;
        let old_layout = self.get_layout();
        let new_layout = Layout::from_size_align(new_capacity, self.inner.alignment)?;
        let prev_base = self.get_base();

        let new_base = unsafe {
            if new_capacity > old_capacity {
                self.inner.alloc.grow(prev_base, old_layout, new_layout)?
            } else {
                self.inner.alloc.shrink(prev_base, old_layout, new_layout)?
            }
        };

        self.inner.base.set(new_base);
        self.inner.capacity.set(new_capacity);
        Ok(if new_base != prev_base {
            Some(new_base.unwrap_or_else(|| unsafe { null_base(new_layout.align()) }))
        } else {
            None
        })
    }

    /// Grows the underlying memory by specified `additional` bytes.
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + additional`.
    ///
    /// # Errors
    ///
    /// [`ContiguousMemoryError::Layout`] error is returned when attempting to
    /// grow the container to a capacity larger than addressable by the target.
    ///
    /// [`ContiguousMemoryError::MemoryManager`] error is returned when
    /// the allocator can't allocate a memory region with required resulting
    /// size because it either exceeds `isize::MAX` or allocator is out of
    /// memory.
    #[inline]
    pub fn reserve(&mut self, additional: usize) -> Result<Option<BasePtr>, ContiguousMemoryError> {
        if additional == 0 {
            return Ok(None);
        }

        let old_capacity = self.get_capacity();
        let new_capacity = old_capacity.saturating_add(additional);

        self.inner.tracker.borrow_mut().grow(new_capacity);
        let old_layout = self.get_layout();
        let new_layout = Layout::from_size_align(new_capacity, self.inner.alignment)?;
        let prev_base = self.get_base();

        let new_base = unsafe { self.inner.alloc.grow(prev_base, old_layout, new_layout)? };

        self.inner.base.set(new_base);
        self.inner.capacity.set(new_capacity);
        Ok(if new_base != prev_base {
            Some(new_base.unwrap_or_else(|| unsafe { null_base(new_layout.align()) }))
        } else {
            None
        })
    }

    pub fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<Option<BasePtr>, ContiguousMemoryError> {
        todo!()
    }

    /// Reserves additional bytes required to store a value with provided
    /// `layout` while keeping it aligned (required padding bytes at the end of
    /// the container will be included).
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + padding + size_of::<V>()`.
    ///
    /// # Errors
    ///
    /// See: [`ContiguousMemory::reserve`]
    pub fn reserve_layout(
        &mut self,
        layout: Layout,
    ) -> Result<Option<BasePtr>, ContiguousMemoryError> {
        match self.get_base() {
            Some(base) => {
                let last =
                    unsafe { (base.as_ptr() as *mut u8).add(self.inner.tracker.borrow().len()) };
                let align_offset = last.align_offset(layout.align());
                self.reserve(align_offset + layout.size())
            }
            None => self.reserve(layout.size()),
        }
    }

    pub fn shrink_to(&mut self, new_capacity: usize) {
        todo!()
    }

    /// Shrinks the allocated memory to fit the currently stored data and
    /// returns the base pointer.
    pub fn shrink_to_fit(&mut self) -> BaseAddress {
        if let Some(new_capacity) = self.inner.tracker.borrow_mut().shrink_to_fit() {
            let prev_base = self.inner.base.get();
            let old_layout = self.get_layout();
            let new_layout = unsafe {
                // SAFETY: Previous layout was valid and had valid alignment,
                // new one is smaller with same alignment so it must be
                // valid as well.
                Layout::from_size_align_unchecked(new_capacity, old_layout.align())
            };
            let new_base = unsafe {
                self.inner
                    .alloc
                    .shrink(prev_base, self.get_layout(), new_layout)
            }
            .expect("unable to shrink allocated memory");
            self.inner.base.set(new_base);
            self.inner.capacity.set(new_capacity);
            new_base
        } else {
            self.get_base()
        }
    }

    /// Stores a `value` of type `T` in the contiguous memory block and returns
    /// a [`reference`](ContiguousEntryRef) to it.
    ///
    /// Value type argument `T` is used to deduce type size and returned
    /// reference dropping behavior.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    pub fn push<T>(&mut self, value: T) -> ContiguousEntryRef<T, A> {
        let mut data = ManuallyDrop::new(value);
        let layout = Layout::for_value(&data);
        let pos = &mut *data as *mut T;

        unsafe { self.push_raw(pos, layout) }
    }

    /// Stores a `value` of type `T` in the contiguous memory block and returns
    /// a reference to it which doesn't mark the memory segment as free when
    /// dropped.
    ///
    /// See [`ContiguousMemory::push`] for details.
    pub fn push_persisted<T>(&mut self, value: T) -> ContiguousEntryRef<T, A> {
        let mut data = ManuallyDrop::new(value);
        let layout = Layout::for_value(&data);
        let pos = &mut *data as *mut T;

        unsafe { self.push_raw_persisted(pos, layout) }
    }

    /// Works same as [`push`](ContiguousMemory::push) but takes a pointer and
    /// layout.
    ///
    /// Pointer type is used to deduce the destruction behavior for
    /// implementations that return a reference, but can be disabled by casting
    /// the provided pointer into `*const ()` type and then calling
    /// [`transmute`](core::mem::transmute) on the returned reference:
    /// ```rust
    /// # use contiguous_mem::*;
    /// # use core::alloc::Layout;
    /// # use core::mem;
    /// # let mut storage = ContiguousMemory::new();
    /// let value = vec!["ignore", "drop", "for", "me"];
    /// let erased = &value as *const Vec<&str> as *const ();
    /// let layout = Layout::new::<Vec<&str>>();
    ///
    /// let stored: CERef<Vec<&str>, DefaultMemoryManager> = unsafe {
    ///     mem::transmute(storage.push_raw(erased, layout))
    /// };
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes or allocation of
    /// additional memory fails.
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
    ) -> ContiguousEntryRef<T, A> {
        let mut tracker = self.inner.tracker.borrow_mut();

        let range = loop {
            let base = self.get_base();
            match tracker.take_next(base, layout) {
                Ok(taken) => {
                    let found = taken.offset_base_unwrap(base);
                    unsafe {
                        core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                    }
                    break taken;
                }
                Err(ContiguousMemoryError::NoStorageLeft) => match base {
                    Some(prev_base) => {
                        let curr_capacity = self.get_capacity();

                        let start_free =
                            (prev_base.as_ptr() as *const u8).add(tracker.last_offset());
                        let padding = start_free.align_offset(layout.align());
                        let increment = padding + layout.size() - tracker.tailing_free_bytes();

                        let new_capacity = curr_capacity
                            .saturating_mul(2)
                            .max(curr_capacity + increment);

                        tracker.grow(new_capacity);
                        let old_layout = self.get_layout();
                        let new_layout = Layout::from_size_align(new_capacity, old_layout.align())
                            .expect("new capacity exceeds `isize::MAX`");

                        let new_base = unsafe {
                            self.inner
                                .alloc
                                .grow(Some(prev_base), old_layout, new_layout)
                        }
                        .expect("unable to allocate required memory");
                        self.inner.base.set(new_base);
                        self.inner.capacity.set(new_capacity);
                    }
                    None => {
                        tracker.grow(layout.size());
                        let new_base = self
                            .inner
                            .alloc
                            .allocate(layout)
                            .expect("pushed element size exceeds `isize::MAX`");
                        self.inner.base.set(new_base);
                        self.inner.capacity.set(layout.size());
                    }
                },
                Err(other) => unreachable!(
                    "reached unexpected error while looking for next region to store data: {:?}",
                    other
                ),
            }
        };

        ContiguousEntryRef {
            inner: Rc::new(ReferenceState {
                state: self.inner.clone(),
                range,
                borrow_kind: Cell::new(BorrowState::Read(0)),
                drop_fn: drop_fn::<T>(),
                _phantom: PhantomData,
            }),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }

    /// Variant of [`push_raw`](ContiguousMemory::push_raw) which returns a
    /// reference that doesn't mark the used memory segment as free when
    /// dropped.
    pub unsafe fn push_raw_persisted<T>(
        &mut self,
        data: *const T,
        layout: Layout,
    ) -> ContiguousEntryRef<T, A> {
        let value = self.push_raw(data, layout);
        let result = value.clone();
        core::mem::forget(value.inner);
        result
    }

    /// Assumes value is stored at the provided _relative_ `position` in
    /// managed memory and returns a pointer or a reference to it.
    ///
    /// # Example
    ///
    /// TODO: Default assume_stored example
    ///
    /// # Safety
    ///
    /// This functions isn't unsafe because creating an invalid pointer isn't
    /// considered unsafe. Responsibility for guaranteeing safety falls on
    /// code that's dereferencing the pointer.
    pub fn assume_stored<T>(&self, position: usize) -> ContiguousEntryRef<T, A> {
        ContiguousEntryRef {
            inner: Rc::new(ReferenceState {
                state: self.inner.clone(),
                range: ByteRange(position, position + size_of::<T>()),
                borrow_kind: Cell::new(BorrowState::Read(0)),
                drop_fn: drop_fn::<T>(),
                _phantom: PhantomData,
            }),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }

    /// Clones the allocated memory region into a new MemoryStorage.
    ///
    /// This function isn't unsafe, even though it ignores presence of `Copy`
    /// bound on stored data, because it doesn't create any invalid references.
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

    /// Marks the entire contents of the container as free, allowing new data
    /// to be stored in place of previously stored data.
    ///
    /// This allows clearing persisted entries created with
    /// [`ContiguousMemory::push_persisted`] and
    /// [`ContiguousMemory::push_raw_persisted`] methods.
    ///
    /// See also:
    /// - [`ContiguousMemory::clear_region`] - for freeing a specific
    ///   container region
    ///
    /// # Safety
    ///
    /// This method is unsafe because it doesn't invalidate any previously
    /// returned references. Storing data into the container and then trying to
    /// access previously stored data from any existing references will cause
    /// undefined behavior.
    pub unsafe fn clear(&mut self) {
        self.inner.tracker.borrow_mut().clear();
    }

    /// Marks the provided `region` of the container as free, allowing new data
    /// to be stored in place of previously stored data.
    ///
    /// This allows clearing persisted entries created with
    /// [`ContiguousMemory::push_persisted`] and
    /// [`ContiguousMemory::push_raw_persisted`] methods.
    ///
    /// See also:
    /// - [`ContiguousMemory::clear`] - for freeing the entire container
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
        self.inner.tracker.borrow_mut().release(region)
    }

    /// Forgets this container without dropping it and returns its base address
    /// and [`Layout`].
    ///
    /// # Safety
    ///
    /// Calling this method will create a memory leak because the smart pointer
    /// to state will not be dropped even when all of the created references go
    /// out of scope. As this method takes ownership of the container, calling
    /// it also ensures that dereferencing pointers created by
    /// [`as_ptr`](refs::ContiguousEntryRef::as_ptr) and related
    /// `ContiguousEntryRef` functions is guaranteed to be safe.
    ///
    /// This method isn't unsafe as leaking data doesn't cause undefined
    /// behavior.
    /// ([_see details_](https://doc.rust-lang.org/nomicon/leaking.html))
    pub fn forget(self) -> (BaseAddress, Layout) {
        let base = self.inner.base.get();
        let layout = self.get_layout();
        core::mem::forget(self);
        (base, layout)
    }
}

#[cfg(feature = "debug")]
impl core::fmt::Debug for ContiguousMemory
where
    MemoryState<ImplDefault>: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ContiguousMemory")
            .field("inner", &self.inner)
            .finish()
    }
}

#[cfg(all(test, not(feature = "no_std")))]
mod test {
    use core::mem::align_of;

    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq)]
    #[repr(C)]
    struct Person {
        name: String,
        last_name: String,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    #[repr(C)]
    struct Car {
        owner: Person,
        driver: Option<Person>,
        cost: u32,
        miles: u32,
    }

    #[test]
    fn construct_contiguous_memory() {
        let memory = ContiguousMemory::new_with_capacity(1024);
        assert_eq!(memory.get_capacity(), 1024);
    }

    #[test]
    fn store_and_get() {
        let mut memory = ContiguousMemory::new_with_capacity(1024);

        let person_a = Person {
            name: "Jerry".to_string(),
            last_name: "Taylor".to_string(),
        };

        let person_b = Person {
            name: "Larry".to_string(),
            last_name: "Taylor".to_string(),
        };

        let car_a = Car {
            owner: person_a.clone(),
            driver: Some(person_b.clone()),
            cost: 20_000,
            miles: 30123,
        };

        let car_b = Car {
            owner: person_b.clone(),
            driver: None,
            cost: 30_000,
            miles: 3780123,
        };

        let value_number = 248169u64;
        let value_string = "This is a test string".to_string();
        let value_byte = 0x41u8;

        let stored_ref_number = memory.push(value_number);
        let stored_ref_car_a = memory.push(car_a.clone());
        let chk_num = &*stored_ref_number.get();
        let chk_car = &*stored_ref_car_a.get();
        let stored_ref_string = memory.push(value_string.clone());

        let stored_ref_byte = memory.push(value_byte);
        let stored_ref_car_b = memory.push(car_b.clone());

        assert_eq!(*stored_ref_number.get(), value_number);
        assert_eq!(*stored_ref_car_a.get(), car_a);
        assert_eq!(*stored_ref_string.get(), value_string);
        assert_eq!(*stored_ref_car_b.get(), car_b);
        assert_eq!(*stored_ref_byte.get(), value_byte);
    }

    #[test]
    fn resize_manually() {
        let mut memory = ContiguousMemory::new_with_capacity(512);

        let person_a = Person {
            name: "Larry".to_string(),
            last_name: "Taylor".to_string(),
        };

        let car_a = Car {
            owner: person_a.clone(),
            driver: Some(person_a),
            cost: 20_000,
            miles: 30123,
        };

        let stored_car = memory.push(car_a.clone());

        assert!(memory.resize(32).is_err());
        memory.resize(1024).unwrap();
        assert_eq!(memory.get_capacity(), 1024);

        assert_eq!(*stored_car.get(), car_a);

        memory.resize(128).unwrap();
        assert_eq!(memory.get_capacity(), 128);

        assert_eq!(*stored_car.get(), car_a);
    }

    #[test]
    fn resize_automatically() {
        let mut memory = ContiguousMemory::new_with_layout(
            Layout::from_size_align(12, align_of::<u64>()).unwrap(),
        );

        {
            let _a = memory.push(1u32);
            let _b = memory.push(2u32);
            let _c = memory.push(3u32);
            assert_eq!(memory.can_push::<u32>(), false);
            let _d = memory.push(4u32);
            assert_eq!(memory.get_capacity(), 24);
        }

        memory.resize(5).expect("can't shrink empty storage");
        {
            memory.push_persisted(1u16);
            memory.push_persisted(2u16);
            assert_eq!(memory.can_push::<u64>(), false);
            memory.push_persisted(3u64);
            assert_eq!(memory.get_capacity(), 16);
        }
    }

    #[test]
    fn add_to_zero_sized() {
        let mut memory = ContiguousMemory::new();

        let person = Person {
            name: "Jacky".to_string(),
            last_name: "Larsson".to_string(),
        };

        let stored_person = memory.push(person.clone());

        assert_eq!(memory.get_capacity(), 48);
        assert_eq!(*stored_person.get(), person);
    }
}
