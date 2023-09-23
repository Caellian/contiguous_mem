#![allow(incomplete_features)]
#![cfg_attr(feature = "no_std", no_std)]
#![cfg_attr(feature = "ptr_metadata", feature(ptr_metadata, unsize))]
#![cfg_attr(feature = "error_in_core", feature(error_in_core))]
#![cfg_attr(doc, feature(doc_auto_cfg))]
#![warn(missing_docs)]
#![doc = include_str!("../doc/crate.md")]

#[cfg(feature = "no_std")]
extern crate alloc;

mod common;
pub mod error;
pub mod range;
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

use common::*;
use common::{ImplConcurrent, ImplDefault, ImplUnsafe};
pub use range::ByteRange;
pub use refs::{CERef, ContiguousEntryRef, SCERef, SyncContiguousEntryRef};
#[cfg(feature = "ptr_metadata")]
pub use types::static_metadata;
use types::*;

use core::cell::Cell;
use core::marker::PhantomData;
use core::{
    alloc::{Layout, LayoutError},
    mem::{size_of, ManuallyDrop},
    ops::Deref,
};

use error::ContiguousMemoryError;

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
pub struct ContiguousMemory {
    inner: Rc<MemoryState<ImplDefault>>,
}

impl ContiguousMemory {
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
            inner: MemoryState::new(base, capacity, alignment),
        })
    }

    /// Creates a new `ContiguousMemory` instance with the provided `layout`.
    pub fn new_for_layout(layout: Layout) -> Self {
        let base = unsafe { allocator::alloc(layout) };
        Self {
            inner: MemoryState::new(base, layout.size(), layout.align()),
        }
    }

    /// Returns the base address of the allocated memory.
    #[inline]
    pub fn get_base(&self) -> *const () {
        self.inner.base.get() as *const ()
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
    /// returning the new base address of the stored items - if `None` is
    /// returned the base address of the memory block is the same.
    ///
    /// Shrinking the container is generally performed in place by freeing
    /// tailing memory space, but growing it can move the data in memory to find
    /// a location that can fit it.
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
        let old_capacity = self.inner.capacity.get();
        if new_capacity == old_capacity {
            return Ok(None);
        }

        self.inner.tracker.borrow_mut().resize(new_capacity)?;
        let layout =
            unsafe { Layout::from_size_align_unchecked(old_capacity, self.inner.alignment) };
        let prev_base = self.inner.base.get();
        let new_base = unsafe { allocator::realloc(prev_base, layout, new_capacity) };
        self.inner.base.set(new_base);
        self.inner.capacity.set(new_capacity);
        Ok(if new_base != prev_base {
            Some(new_base as *const ())
        } else {
            None
        })
    }

    /// Reserves `additional` bytes.
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
        let last = unsafe { self.inner.base.get().add(self.inner.tracker.borrow().len()) };
        let align_offset = last.align_offset(layout.align());
        self.reserve(align_offset + layout.size())
    }

    /// Reserves additional bytes required to store a value of type `V`.
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + size_of::<V>()`.
    #[inline]
    pub fn reserve_type<V>(&mut self) -> Option<*const ()> {
        self.reserve_layout(Layout::new::<V>())
    }

    /// Reserves additional bytes required to store `count` number of
    /// values of type `V`.
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + leading_padding + size_of::<V>() * count  + internal_padding * (count - 1)`.
    pub fn reserve_type_count<V>(&mut self, count: usize) -> Option<*const ()> {
        let layout = Layout::new::<V>();
        let last = unsafe { self.inner.base.get().add(self.inner.tracker.borrow().len()) };
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
        if let Some(new_capacity) = self.inner.tracker.borrow_mut().shrink_to_fit() {
            let prev_base = self.inner.base.get();
            let new_base =
                unsafe { allocator::realloc(prev_base, self.get_layout(), new_capacity) };
            self.inner.base.set(new_base);
            self.inner.capacity.set(new_capacity);
            new_capacity
        } else {
            self.inner.capacity.get()
        }
    }

    /// Stores a `value` of type `T` in the contiguous memory block and returns
    /// a [`reference`](ContiguousEntryRef) to it.
    ///
    /// Value type argument `T` is used to deduce type size and returned
    /// reference dropping behavior.
    pub fn push<T>(&mut self, value: T) -> ContiguousEntryRef<T> {
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
    pub fn push_persisted<T>(&mut self, value: T) -> ContiguousEntryRef<T> {
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
    pub unsafe fn push_raw<T>(&mut self, data: *const T, layout: Layout) -> ContiguousEntryRef<T> {
        let mut tracker = self.inner.tracker.borrow_mut();

        let range = loop {
            let base = self.get_base() as usize;
            match tracker.take_next(base, layout) {
                Ok(taken) => {
                    let found = (taken.0 + base) as *mut u8;
                    unsafe {
                        core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                    }
                    break taken;
                }
                Err(ContiguousMemoryError::NoStorageLeft) => {
                    let curr_capacity = self.inner.capacity.get();

                    let prev_base = self.inner.base.get();
                    let start_free = prev_base.add(tracker.last_offset());
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
                        unsafe { allocator::realloc(prev_base, storage_layout, new_capacity) };
                    self.inner.base.set(new_base);
                    self.inner.capacity.set(new_capacity);
                }
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
    ) -> ContiguousEntryRef<T> {
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
    pub fn assume_stored<T>(&self, position: usize) -> ContiguousEntryRef<T> {
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

    /// Marks the entire contents of the container as free, allowing new data
    /// to be stored in place of previously stored data.
    ///
    /// This allows clearing persisted entries created with
    /// [`ContiguousMemory::push_persisted`] and
    /// [`ContiguousMemory::push_raw_persisted`] methods.
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
    /// [`as_ptr`](refs::ContiguousEntryRef::as_ptr),
    /// [`as_ptr_mut`](refs::ContiguousEntryRef::as_ptr_mut),
    /// [`into_ptr`](refs::ContiguousEntryRef::into_ptr), and
    /// [`into_ptr_mut`](refs::ContiguousEntryRef::into_ptr_mut)
    /// `ContiguousEntryRef` methods is guaranteed to be safe.
    ///
    /// This method isn't unsafe as leaking data doesn't cause undefined
    /// behavior.
    /// ([_see details_](https://doc.rust-lang.org/nomicon/leaking.html))
    pub fn forget(self) -> (*const (), Layout) {
        let base = self.inner.base.get();
        let layout = self.get_layout();
        core::mem::forget(self);
        (base as *const (), layout)
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

pub(crate) mod sealed {
    use core::cell::{Cell, RefCell};

    use crate::tracker::AllocationTracker;

    use super::*;

    #[derive(Clone, PartialEq, Eq)]
    #[repr(transparent)]
    pub(crate) struct BaseLocation<Impl: StorageDetails>(pub(crate) Impl::Base);

    #[cfg(feature = "debug")]
    impl<Impl: StorageDetails> core::fmt::Debug for BaseLocation<Impl>
    where
        Impl::LockResult<*mut u8>: core::fmt::Debug,
    {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.debug_tuple("BaseLocation")
                .field(&Impl::get_base(&self.0))
                .finish()
        }
    }

    impl<Impl: ImplDetails> Deref for BaseLocation<Impl> {
        type Target = <Impl as StorageDetails>::Base;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl Copy for BaseLocation<ImplUnsafe> {}
    unsafe impl<Impl: ImplDetails> Send for BaseLocation<Impl> where Impl: PartialEq<ImplConcurrent> {}
    unsafe impl<Impl: ImplDetails> Sync for BaseLocation<Impl> where Impl: PartialEq<ImplConcurrent> {}

    #[repr(C)]
    pub struct MemoryState<Impl: StorageDetails = ImplDefault> {
        pub(crate) base: BaseLocation<Impl>,
        pub(crate) capacity: Impl::SizeType,
        pub(crate) alignment: usize,
        pub(crate) tracker: Impl::AllocationTracker,
    }

    impl<Impl: StorageDetails> core::fmt::Debug for MemoryState<Impl>
    where
        BaseLocation<Impl>: core::fmt::Debug,
        Impl::SizeType: core::fmt::Debug,
        Impl::AllocationTracker: core::fmt::Debug,
    {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.debug_struct("ContiguousMemoryState")
                .field("base", &self.base)
                .field("capacity", &self.capacity)
                .field("alignment", &self.alignment)
                .field("tracker", &self.tracker)
                .finish()
        }
    }

    impl<Impl: StorageDetails> MemoryState<Impl> {
        /// Returns the layout of the managed memory.
        pub fn layout(&self) -> Layout {
            unsafe {
                let capacity = Impl::get_capacity(core::mem::transmute(self));
                Layout::from_size_align_unchecked(capacity, self.alignment)
            }
        }
    }

    impl MemoryState<ImplDefault> {
        pub fn new(base: *mut u8, capacity: usize, alignment: usize) -> Rc<Self> {
            Rc::new(MemoryState {
                base: BaseLocation(Cell::new(base)),
                capacity: Cell::new(capacity),
                alignment,
                tracker: RefCell::new(AllocationTracker::new(capacity)),
            })
        }
    }

    impl MemoryState<ImplConcurrent> {
        pub fn new_concurrent(base: *mut u8, capacity: usize, alignment: usize) -> Arc<Self> {
            Arc::new(MemoryState {
                base: BaseLocation(RwLock::new(base)),
                capacity: AtomicUsize::new(capacity),
                alignment,
                tracker: Mutex::new(AllocationTracker::new(capacity)),
            })
        }
    }

    impl MemoryState<ImplUnsafe> {
        pub fn new_unsafe(base: *mut u8, capacity: usize, alignment: usize) -> Self {
            MemoryState {
                base: BaseLocation(base),
                capacity,
                alignment,
                tracker: AllocationTracker::new(capacity),
            }
        }
    }

    impl Clone for MemoryState<ImplUnsafe> {
        fn clone(&self) -> Self {
            Self {
                base: self.base,
                capacity: self.capacity,
                alignment: self.alignment,
                tracker: self.tracker.clone(),
            }
        }
    }

    impl<Impl: StorageDetails> Drop for MemoryState<Impl> {
        fn drop(&mut self) {
            let layout = self.layout();
            Impl::deallocate(&mut self.base.0, layout)
        }
    }
}
use crate::refs::sealed::{BorrowState, ReferenceState};
pub(crate) use sealed::*;

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
        let memory = ContiguousMemory::new(1024);
        assert_eq!(memory.get_capacity(), 1024);
    }

    #[test]
    fn store_and_get() {
        let mut memory = ContiguousMemory::new(1024);

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
        let mut memory = ContiguousMemory::new(512);

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
        let mut memory = ContiguousMemory::new_aligned(12, align_of::<u64>()).unwrap();

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
        let mut memory = ContiguousMemory::new(0);

        let person = Person {
            name: "Jacky".to_string(),
            last_name: "Larsson".to_string(),
        };

        let stored_person = memory.push(person.clone());

        assert_eq!(memory.get_capacity(), 48);
        assert_eq!(*stored_person.get(), person);
    }
}
