#![allow(incomplete_features)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(
    feature = "ptr_metadata",
    feature(ptr_metadata, unsize, specialization)
)]
#![cfg_attr(feature = "error_in_core", feature(error_in_core))]
#![cfg_attr(doc, feature(doc_auto_cfg))]
#![warn(missing_docs)]
#![doc = include_str!("../doc/crate.md")]

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(all(not(feature = "std"), not(feature = "no_std")))]
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
use refs::{ContiguousMemoryRef, SyncContiguousMemoryRef};
use types::*;

#[doc(inline)]
pub use tracker::AllocationTracker;

use core::{
    alloc::{Layout, LayoutError},
    mem::{size_of, ManuallyDrop},
    ops::Deref,
};

use error::{ContiguousMemoryError, LockingError};

/// Re-exports commonly used types.
pub mod prelude {
    pub use crate::{
        error::*, range::ByteRange, refs::*, ContiguousMemory, ContiguousMemoryStorage,
        ImplConcurrent, ImplDefault, ImplDetails, ImplUnsafe, StoreData, SyncContiguousMemory,
        UnsafeContiguousMemory,
    };
}

/// A memory container for efficient allocation and storage of contiguous data.
///
/// This collection manages a contiguous block of memory, allowing for storage
/// of arbitrary data types while ensuring that stored items are placed
/// adjacently and ensuring they're properly alligned.
///
/// Type argument `Impl` specifies implementation details for the behavior of
/// this struct. This struct also implements [`StoreData`] for all of the
/// details which specifies underlying logic for storing items.
///
/// Note that this structure is a smart abstraction over underlying data,
/// copying it creates a copy which represents the same internal state.
#[cfg_attr(feature = "debug", derive(Debug))]
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

    /// Returns the base address (`*mut u8`) of the allocated memory.
    ///
    /// # Errors
    ///
    /// For [concurrent implementation](ImplConcurrent) this function can return
    /// [LockingError::Poisoned](crate::LockingError::Poisoned) if the mutex
    /// holding the base address has been poisoned.
    pub fn get_base(&self) -> Impl::LockResult<*mut u8> {
        Impl::get_base(&self.inner)
    }

    /// Returns the current capacity of the memory container.
    ///
    /// The capacity represents the size of the memory block that has been
    /// allocated for storing data. It may be larger than the amount of data
    /// currently stored within the container.
    pub fn get_capacity(&self) -> usize {
        Impl::get_capacity(Impl::deref_state(&self.inner))
    }

    /// Returns the layout of the memory region containing stored data.
    pub fn get_layout(&self) -> Layout {
        Impl::deref_state(&self.inner).layout()
    }

    /// Resizes the memory container to the specified `new_capacity`, optionally
    /// returning the new base address of the stored items.
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
    /// This function can return the following errors:
    ///
    /// - [`ContiguousMemoryError::Unshrinkable`]: Returned when attempting to
    ///   shrink the memory container, but the stored data prevents the
    ///   container from being shrunk to the desired capacity.
    ///
    /// - [`ContiguousMemoryError::Lock`]: Returned if the mutex holding the
    ///   base address or the [`AllocationTracker`] is poisoned.
    ///
    /// [`AllocationTracker`]: crate::tracker::AllocationTracker
    pub fn resize(
        &mut self,
        new_capacity: usize,
    ) -> Result<Option<*mut u8>, ContiguousMemoryError> {
        if new_capacity == Impl::get_capacity(Impl::deref_state(&self.inner)) {
            return Ok(None);
        }

        let old_capacity = Impl::get_capacity(Impl::deref_state(&self.inner));
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

    /// Stores a `value` of type `T` in the contiguous memory block.
    ///
    /// Value type is used to deduce type size and returned reference dropping
    /// behavior.
    ///
    /// Returned value is implementation specific:
    /// - For [concurrent implementation] it is
    ///   `Result<SyncContiguousMemoryRef<T>, LockingError>`,
    /// - For [default implementation] it is `ContiguousMemoryRef<T>`,
    /// - For [fixed implementation] it is
    ///   `Result<*mut u8, ContiguousMemoryError>`.
    ///
    /// [concurrent implementation]: struct.ContiguousMemory.html#method.store_data-1
    /// [default implementation]: struct.ContiguousMemory.html#method.store_data
    /// [fixed implementation]: struct.ContiguousMemory.html#method.store_data-2
    pub fn store<T: StoreRequirements>(
        &mut self,
        value: T,
    ) -> <Impl as StorageDetails>::StoreResult<T>
    where
        Self: StoreData<Impl>,
    {
        let mut data = ManuallyDrop::new(value);
        let layout = Layout::for_value(&data);
        let pos = &mut *data as *mut T;
        let result = unsafe { self.store_data(pos, layout) };
        result
    }

    /// Returns `true` if the provided value can be stored.
    ///
    /// If the [`AllocationTracker`] can't be immutably accesed, a
    /// [`ContiguousMemoryError::TrackerInUse`] error is returned.
    ///
    /// For concurrent implementation a [`ContiguousMemoryError::Lock`] is
    /// returned under same conditions.
    ///
    /// Unsafe implementation never fails.
    pub fn can_store<T: StoreRequirements>(
        &self,
        value: &T,
    ) -> Result<bool, ContiguousMemoryError> {
        let layout = Layout::for_value(&value);
        Ok(Impl::peek_next(&self.inner, layout)?.is_some())
    }
}

/// Trait for specializing store function across implementations.
pub trait StoreData<Impl: ImplDetails> {
    /// Works same as [`store`](ContiguousMemory::store) but takes a pointer and
    /// layout.
    ///
    /// Pointer type is used to deduce the destruction behavior for
    /// implementations that return a reference, but can be disabled by casting
    /// the provided pointer into `*mut ()` type and then calling
    /// [`core::mem::transmute`] on the returned reference.
    unsafe fn store_data<T: StoreRequirements>(
        &mut self,
        data: *mut T,
        layout: Layout,
    ) -> <Impl as StorageDetails>::StoreResult<T>;
}

impl StoreData<ImplConcurrent> for ContiguousMemoryStorage<ImplConcurrent> {
    /// Returns a [`SyncContiguousMemoryRef`] pointing to the stored value, or a
    /// [`LockingError::Poisoned`] error when the [`AllocationTracker`]
    /// associated with the memory container is poisoned.
    ///
    /// [`AllocationTracker`]: crate::tracker::AllocationTracker
    unsafe fn store_data<T: StoreRequirements>(
        &mut self,
        data: *mut T,
        layout: Layout,
    ) -> Result<SyncContiguousMemoryRef<T>, LockingError> {
        let (addr, range) = loop {
            match ImplConcurrent::store_next(&mut self.inner, layout) {
                Ok(taken) => {
                    let found =
                        (taken.0 + ImplConcurrent::get_base(&self.inner)? as usize) as *mut u8;
                    unsafe { core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size()) }
                    break (found, taken);
                }
                Err(ContiguousMemoryError::NoStorageLeft) => {
                    match self.resize(ImplConcurrent::get_capacity(&self.inner) * 2) {
                        Ok(_) => {}
                        Err(ContiguousMemoryError::Lock(locking_err)) => return Err(locking_err),
                        Err(other) => unreachable!(
                            "reached unexpected error while growing the container to store data: {:?}",
                            other
                        ),
                    };
                }
                Err(ContiguousMemoryError::Lock(locking_err)) => return Err(locking_err),
                Err(other) => unreachable!(
                    "reached unexpected error while looking for next region to store data: {:?}",
                    other
                ),
            }
        };

        Ok(ImplConcurrent::build_ref(
            &self.inner,
            addr as *mut T,
            &range,
        ))
    }
}

impl StoreData<ImplDefault> for ContiguousMemoryStorage<ImplDefault> {
    /// Returns a [`ContiguousMemoryRef`] pointing to the stored value.
    unsafe fn store_data<T: StoreRequirements>(
        &mut self,
        data: *mut T,
        layout: Layout,
    ) -> ContiguousMemoryRef<T> {
        let (addr, range) = loop {
            match ImplDefault::store_next(&mut self.inner, layout) {
                Ok(taken) => {
                    let found = (taken.0 + self.base.get() as usize) as *mut u8;
                    unsafe {
                        core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                    }
                    break (found, taken);
                }
                Err(ContiguousMemoryError::NoStorageLeft) => {
                    match self.resize(ImplDefault::get_capacity(&self.inner) * 2) {
                        Ok(_) => {},
                        Err(err) => unreachable!(
                            "reached unexpected error while growing the container to store data: {:?}",
                            err
                        ),
                    }
                }
                Err(other) => unreachable!(
                    "reached unexpected error while looking for next region to store data: {:?}",
                    other
                ),
            }
        };

        ImplDefault::build_ref(&self.inner, addr as *mut T, &range)
    }
}

impl StoreData<ImplUnsafe> for ContiguousMemoryStorage<ImplUnsafe> {
    /// Returns a raw pointer (`*mut T`) to the stored value or a
    /// [`ContiguousMemoryError::NoStorageLeft`] indicating that the container
    /// couldn't store the provided data with current size.
    ///
    /// Memory block can still be grown by calling [`ContiguousMemory::resize`],
    /// but it can't be done automatically as that would invalidate all the
    /// existing pointers without any indication.
    unsafe fn store_data<T: StoreRequirements>(
        &mut self,
        data: *mut T,
        layout: Layout,
    ) -> Result<*mut T, ContiguousMemoryError> {
        let (addr, range) = loop {
            match ImplUnsafe::store_next(&mut self.inner, layout) {
                Ok(taken) => {
                    let found = (taken.0 + *self.base as usize) as *mut u8;
                    unsafe {
                        core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                    }
                    break (found, taken);
                }
                Err(other) => return Err(other),
            }
        };

        Ok(ImplUnsafe::build_ref(&self.inner, addr as *mut T, &range))
    }
}

impl ContiguousMemoryStorage<ImplUnsafe> {
    /// Allows freeing a memory range stored at provided `position`.
    ///
    /// Type of the position pointer `T` determines the size of the freed chunk.
    #[inline(always)]
    pub unsafe fn free_typed<T>(&mut self, position: *mut T) {
        Self::free(self, position, size_of::<T>())
    }

    /// Allows freeing a memory range stored at provided `position` with the
    /// specified `size`.
    pub unsafe fn free<T>(&mut self, position: *mut T, size: usize) {
        let pos: usize = position.sub(self.get_base() as usize) as usize;
        if let Some(freed) = ImplUnsafe::free_region(&mut self.inner, ByteRange(pos, pos + size)) {
            core::ptr::drop_in_place(freed as *mut T);
        }
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

    #[cfg_attr(feature = "debug", derive(Debug))]
    #[derive(Clone, PartialEq, Eq)]
    #[repr(transparent)]
    pub(crate) struct BaseLocation<Impl: StorageDetails>(pub(crate) Impl::Base);

    impl<Impl: ImplDetails> Deref for BaseLocation<Impl> {
        type Target = <Impl as StorageDetails>::Base;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl Copy for BaseLocation<ImplUnsafe> {}
    unsafe impl<Impl: ImplDetails> Send for BaseLocation<Impl> where Impl: PartialEq<ImplConcurrent> {}
    unsafe impl<Impl: ImplDetails> Sync for BaseLocation<Impl> where Impl: PartialEq<ImplConcurrent> {}

    #[cfg_attr(feature = "debug", derive(Debug))]
    #[repr(C)]
    pub struct ContiguousMemoryState<Impl: StorageDetails = ImplDefault> {
        pub(crate) base: BaseLocation<Impl>,
        pub(crate) size: Impl::SizeType,
        pub(crate) alignment: usize,
        pub(crate) tracker: Impl::AllocationTracker,
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
                size: self.size,
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

#[cfg(all(test, feature = "std"))]
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

        let stored_ref_number = memory.store(value_number);
        let stored_ref_car_a = memory.store(car_a.clone());
        let stored_ref_string = memory.store(value_string.clone());
        let stored_ref_byte = memory.store(value_byte);
        let stored_ref_car_b = memory.store(car_b.clone());

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

        let stored_car = memory.store(car_a.clone());

        assert!(memory.resize(32).is_err());
        memory.resize(1024).unwrap();
        assert_eq!(memory.get_capacity(), 1024);

        assert_eq!(*stored_car.get(), car_a);

        memory.resize(128).unwrap();
        assert_eq!(memory.get_capacity(), 128);

        assert_eq!(*stored_car.get(), car_a);
    }
}
