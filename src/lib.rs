#![allow(incomplete_features)]
#![cfg_attr(feature = "no_std", no_std)]
#![cfg_attr(
    feature = "ptr_metadata",
    feature(ptr_metadata, unsize, specialization)
)]
#![cfg_attr(feature = "error_in_core", feature(error_in_core))]
#![cfg_attr(doc, feature(doc_auto_cfg))]
#![warn(missing_docs)]
#![doc = include_str!("../doc/crate.md")]

#[cfg(feature = "no_std")]
extern crate alloc;

#[cfg(all(feature = "no_std", not(feature = "no_std")))]
compile_error!(
    "contiguous_mem: please enable 'no_std' feature to enable 'no_std' dependencies, or the default 'std' feature"
);

pub(crate) mod details;
pub use details::{ImplConcurrent, ImplDefault, ImplDetails, ImplUnsafe};

pub mod error;
pub mod range;
pub mod refs;
pub mod tracker;
mod types;

use details::*;
#[doc(inline)]
pub use range::ByteRange;
use types::*;

#[doc(inline)]
pub use tracker::AllocationTracker;

use core::{
    alloc::{Layout, LayoutError},
    mem::{size_of, ManuallyDrop},
    ops::Deref,
};

use error::ContiguousMemoryError;

/// Re-exports commonly used types.
pub mod prelude {
    pub use crate::{
        error::*, range::ByteRange, refs::*, ContiguousMemory, ContiguousMemoryStorage,
        ImplConcurrent, ImplDefault, ImplUnsafe, SyncContiguousMemory, UnsafeContiguousMemory,
    };
}

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
/// [`ContiguousMemoryStorage::copy_storage`]
pub struct ContiguousMemoryStorage<Impl: ImplDetails = ImplDefault> {
    inner: Impl::StorageState,
}

impl<Impl: ImplDetails> ContiguousMemoryStorage<Impl> {
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
        Ok(ContiguousMemoryStorage {
            inner: Impl::build_state(base, capacity, alignment)?,
        })
    }

    /// Creates a new `ContiguousMemory` instance with the provided `layout`.
    pub fn new_from_layout(layout: Layout) -> Result<Self, LayoutError> {
        let base = unsafe { allocator::alloc(layout) };
        Ok(ContiguousMemoryStorage {
            inner: Impl::build_state(base, layout.size(), layout.align())?,
        })
    }

    /// Returns the base address (`*mut u8`) of the allocated memory.
    ///
    /// # Errors
    ///
    /// For [concurrent implementation](ImplConcurrent) this function can return
    /// [`LockingError::Poisoned`](crate::error::LockingError::Poisoned) if the
    /// mutex holding the base address has been poisoned.
    pub fn get_base(&self) -> Impl::LockResult<*mut u8> {
        Impl::get_base(&self.base)
    }

    /// Returns the current capacity of the memory container.
    ///
    /// The capacity represents the size of the memory block that has been
    /// allocated for storing data. It may be larger than the amount of data
    /// currently stored within the container.
    #[must_use]
    pub fn get_capacity(&self) -> usize {
        Impl::get_capacity(&self.capacity)
    }

    /// Returns the layout of the memory region containing stored data.
    #[must_use]
    pub fn get_layout(&self) -> Layout {
        Impl::deref_state(&self.inner).layout()
    }

    /// Resizes the memory container to the specified `new_capacity`, optionally
    /// returning the new base address of the stored items - if `None` is
    /// returned the base address of the memory block is the same.
    ///
    /// Shrinking the container is generally performed in place by freeing
    /// tailing memory space, but growing it can move the data in memory to find
    /// a location that can fit it.
    ///
    /// [Unsafe implementation](ImplUnsafe) should match on the returned value
    /// and update any existing pointers accordingly.
    ///
    /// # Errors
    ///
    /// [`ContiguousMemoryError::Unshrinkable`] error is returned when
    /// attempting to shrink the memory container, but previously stored data
    /// prevents the container from being shrunk to the desired capacity.
    ///
    /// In a concurrent implementation [`ContiguousMemoryError::Lock`] is
    /// returned if the mutex holding the base address or the
    /// [`AllocationTracker`](crate::tracker::AllocationTracker) is poisoned.
    pub fn resize(
        &mut self,
        new_capacity: usize,
    ) -> Result<Option<*mut u8>, ContiguousMemoryError> {
        if new_capacity == Impl::get_capacity(&self.capacity) {
            return Ok(None);
        }

        let old_capacity = Impl::get_capacity(&self.capacity);
        Impl::resize_tracker(&mut self.inner, new_capacity)?;
        let moved = match Impl::resize_container(&mut self.inner, new_capacity) {
            Ok(it) => it,
            Err(ContiguousMemoryError::Lock(lock_err)) if Impl::USES_LOCKS => {
                Impl::resize_tracker(&mut self.inner, old_capacity)?;
                return Err(ContiguousMemoryError::Lock(lock_err));
            }
            Err(other) => return Err(other),
        };

        Ok(moved)
    }

    /// Shrinks the allocated memory to fit the currently stored data.
    pub fn shrink_to_fit(&mut self) -> Result<(), ContiguousMemoryError> {
        if let Some(shrunk) = Impl::shrink_tracker(&mut self.inner)? {
            self.resize(shrunk)?;
        }
        Ok(())
    }

    /// Returns `true` if the provided value can be stored without growing the
    /// container.
    ///
    /// It's usually better to try storing the value directly and then handle
    /// the case where it wasn't stored (for unsafe implementation).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use contiguous_mem::UnsafeContiguousMemory;
    /// # use core::mem::size_of_val;
    /// let mut storage = UnsafeContiguousMemory::new(0);
    /// let value = [2, 4, 8, 16];
    ///
    /// # assert_eq!(storage.can_store(&value).unwrap(), false);
    /// if !storage.can_store(&value).unwrap() {
    ///     storage.resize(storage.get_capacity() + size_of_val(&value));
    ///
    ///     // ...update old pointers...
    /// }
    ///
    /// let stored_value =
    ///   storage.store(value).expect("unable to store after growing the container");
    /// ```
    ///
    /// # Errors
    ///
    /// If the [`AllocationTracker`] can't be immutably accesed, a
    /// [`ContiguousMemoryError::TrackerInUse`] error is returned.
    ///
    /// For concurrent implementation a [`ContiguousMemoryError::Lock`] is
    /// returned under same conditions.
    ///
    /// Unsafe implementation never fails.
    pub fn can_push<T: StoreRequirements>(&self, value: &T) -> Result<bool, ContiguousMemoryError> {
        let layout = Layout::for_value(&value);
        Ok(Impl::peek_next(&self.inner, layout)?.is_some())
    }

    /// Stores a `value` of type `T` in the contiguous memory block and returns
    /// a reference or a pointer pointing to it.
    ///
    /// Value type argument `T` is used to deduce type size and returned
    /// reference dropping behavior.
    ///
    /// Returned value is implementation specific:
    /// - For concurrent implementation it is
    ///   `Result<SyncContiguousEntryRef<T>, LockingError>`,
    /// - For default implementation it is `ContiguousEntryRef<T>`,
    /// - For unsafe implementation it is
    ///   `Result<*mut u8, ContiguousMemoryError>`.
    ///
    /// # Errors
    ///
    /// ## Concurrent implementation
    ///
    /// Concurrent implementation returns a
    /// [`LockingError::Poisoned`](crate::error::LockingError::Poisoned) error
    /// when the [`AllocationTracker`] associated with the memory container is
    /// poisoned.
    ///
    /// ## Unsafe implementation
    ///
    /// Unsafe implementation returns a [`ContiguousMemoryError::NoStorageLeft`]
    /// indicating that the container couldn't store the provided data with
    /// current size.
    ///
    /// Memory block can still be grown by calling [`ContiguousMemory::resize`],
    /// but it can't be done automatically as that would invalidate all the
    /// existing pointers without any indication.
    pub fn push<T: StoreRequirements>(&mut self, value: T) -> Impl::StoreResult<T> {
        let mut data = ManuallyDrop::new(value);
        let layout = Layout::for_value(&data);
        let pos = &mut *data as *mut T;
        let result = unsafe { self.push_raw(pos, layout) };
        result
    }

    /// Works same as [`store`](ContiguousMemory::push) but takes a pointer and
    /// layout.
    ///
    /// Pointer type is used to deduce the destruction behavior for
    /// implementations that return a reference, but can be disabled by casting
    /// the provided pointer into `*mut ()` type and then calling
    /// [`core::mem::transmute`] on the returned reference.
    pub unsafe fn push_raw<T: StoreRequirements>(
        &mut self,
        data: *mut T,
        layout: Layout,
    ) -> Impl::StoreResult<T> {
        Impl::push_raw(&mut self.inner, data, layout)
    }

    /// Assumes value is stored at the provided _relative_ `position` in
    /// managed memory and returns a pointer or a reference to it.
    ///
    /// This functions isn't unsafe because creating an invalid pointer isn't
    /// considered unsafe. Responsibility for guaranteeing safety falls on
    /// code that's dereferencing the pointer.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use contiguous_mem::UnsafeContiguousMemory;
    /// let mut storage = UnsafeContiguousMemory::new(128);
    /// let initial_position = storage.store(278u32).unwrap();
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
    pub fn assume_stored<T: StoreRequirements>(
        &self,
        position: usize,
    ) -> Impl::LockResult<Impl::ReferenceType<T>> {
        Impl::assume_stored(&self.inner, position)
    }

    /// Forgets this container without dropping it.
    ///
    /// Calling this method will create a memory leak because the smart pointer
    /// to state will not be dropped even when all of the created references go
    /// out of scope. As this method takes ownership of the container, calling
    /// it also ensures that dereferencing pointers created by
    /// [`as_ptr`](ContiguousEntryReference::as_ptr),
    /// [`as_ptr_mut`](ContiguousEntryReference::as_ptr_mut),
    /// [`into_ptr`](ContiguousEntryReference::into_ptr), and
    /// [`into_ptr_mut`](ContiguousEntryReference::into_ptr_mut)
    /// `ContiguousEntryReference` methods is guaranteed to be safe.
    ///
    /// This method isn't unsafe as leaking data doesn't cause undefined
    /// behavior.
    /// ([_see details_](https://doc.rust-lang.org/nomicon/leaking.html))
    pub fn forget(self) {
        core::mem::forget(self);
    }
}

impl ContiguousMemoryStorage<ImplUnsafe> {
    /// Clones the allocated memory region into a new ContiguousMemoryStorage.
    ///
    /// This function isn't unsafe, even though it ignores presence of `Copy`
    /// bound on stored data, because it doesn't create any pointers.
    #[must_use]
    pub fn copy_data(&self) -> Self {
        let current_layout = self.get_layout();
        let result = Self::new_from_layout(current_layout).expect("current layout should be valid");
        unsafe {
            core::ptr::copy_nonoverlapping(
                self.get_base(),
                result.get_base(),
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
        let pos: usize = position.sub(self.get_base() as usize) as usize;
        if let Some(freed) = ImplUnsafe::free_region(&mut self.inner, ByteRange(pos, pos + size)) {
            core::ptr::drop_in_place(freed as *mut T);
        }
    }
}

#[cfg(feature = "debug")]
impl<Impl: ImplDetails> core::fmt::Debug for ContiguousMemoryStorage<Impl>
where
    Impl::StorageState: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ContiguousMemoryStorage")
            .field("inner", &self.inner)
            .finish()
    }
}

impl<Impl: ImplDetails> Clone for ContiguousMemoryStorage<Impl> {
    fn clone(&self) -> Self {
        ContiguousMemoryStorage {
            inner: self.inner.clone(),
        }
    }
}

impl<Impl: ImplDetails> Deref for ContiguousMemoryStorage<Impl> {
    type Target = ContiguousMemoryState<Impl>;

    fn deref(&self) -> &Self::Target {
        Impl::deref_state(&self.inner)
    }
}

pub(crate) mod sealed {
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
    pub struct ContiguousMemoryState<Impl: StorageDetails = ImplDefault> {
        pub(crate) base: BaseLocation<Impl>,
        pub(crate) capacity: Impl::SizeType,
        pub(crate) alignment: usize,
        pub(crate) tracker: Impl::AllocationTracker,
    }

    impl<Impl: StorageDetails> core::fmt::Debug for ContiguousMemoryState<Impl>
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

    impl<Impl: StorageDetails> ContiguousMemoryState<Impl> {
        /// Returns the layout of the managed memory.
        pub fn layout(&self) -> Layout {
            unsafe {
                let capacity = Impl::get_capacity(core::mem::transmute(self));
                Layout::from_size_align_unchecked(capacity, self.alignment)
            }
        }
    }

    impl Clone for ContiguousMemoryState<ImplUnsafe> {
        fn clone(&self) -> Self {
            Self {
                base: self.base,
                capacity: self.capacity,
                alignment: self.alignment,
                tracker: self.tracker.clone(),
            }
        }
    }

    impl<Impl: StorageDetails> Drop for ContiguousMemoryState<Impl> {
        fn drop(&mut self) {
            let layout = self.layout();
            Impl::deallocate(&mut self.base.0, layout)
        }
    }
}
use sealed::*;

/// A type alias for [`ContiguousMemoryStorage`] that enables references to data
/// stored within it to be used safely across multiple threads.
///
/// # Example
///
/// ```rust
#[doc = include_str!("../examples/sync_impl.rs")]
/// ```
pub type SyncContiguousMemory = ContiguousMemoryStorage<ImplConcurrent>;

/// A type alias for [`ContiguousMemoryStorage`] that offers a synchronous
/// implementation without using internal mutexes making it faster but not
/// thread safe.
///
/// # Example
///
/// ```rust
#[doc = include_str!("../examples/default_impl.rs")]
/// ```
pub type ContiguousMemory = ContiguousMemoryStorage<ImplDefault>;

/// A type alias for [`ContiguousMemoryStorage`] that provides a
/// minimal and unsafe implementation. Suitable when the container is guaranteed
/// to outlive any returned pointers.
///
/// # Example
///
/// ```rust
#[doc = include_str!("../examples/unsafe_impl.rs")]
/// ```
pub type UnsafeContiguousMemory = ContiguousMemoryStorage<ImplUnsafe>;

#[cfg(all(test, not(feature = "no_std")))]
mod test {
    use super::prelude::*;

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
    fn test_new_contiguous_memory() {
        let memory = ContiguousMemory::new(1024);
        assert_eq!(memory.get_capacity(), 1024);
    }

    #[test]
    fn test_store_and_get_contiguous_memory() {
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
    fn test_resize_contiguous_memory() {
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
}
