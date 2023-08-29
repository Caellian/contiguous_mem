#![allow(incomplete_features)]
#![cfg_attr(feature = "no_std", no_std)]
#![cfg_attr(
    feature = "ptr_metadata",
    feature(ptr_metadata, unsize, specialization)
)]
#![cfg_attr(feature = "error_in_core", feature(error_in_core))]

#[cfg(feature = "no_std")]
extern crate alloc;

#[cfg(any(
    all(not(feature = "std"), not(feature = "no_std")),
    all(feature = "std", feature = "no_std")
))]
compile_error!(
    "contiguous_mem: either 'std' or 'no_std' feature must be enabled, not both or neither"
);

pub mod details;
pub mod error;
pub mod range;
pub mod tracker;
mod types;

use details::*;
use range::ByteRange;
use types::*;

#[cfg(feature = "ptr_metadata")]
pub use types::pointer as ptr_metadata_ext;

use core::{
    alloc::{Layout, LayoutError},
    marker::PhantomData,
    mem::{size_of, ManuallyDrop},
    ops::DerefMut,
};

use error::{ContiguousMemoryError, LockingError, MutablyBorrowed};

/// A memory container for efficient allocation and storage of contiguous data.
///
/// This structure manages a contiguous block of memory, allowing for the
/// storage of arbitrary data while ensuring that stored items are placed
/// adjacently without imposing any restrictions on layout, such as those found
/// in memory pools or the standard library's [Vec].
///
/// The `ContiguousMemory` type is particularly useful for scenarios where data
/// locality and efficient memory usage are crucial, as it provides a means to
/// allocate and manage memory in a linear fashion.
///
/// # Performance
///
/// The [`store`] operation has a generally constant time complexity when
/// storing items with the same layout, as it primarily involves finding
/// available memory regions. The time complexity increases linearly with the
/// number of gaps between previously stored items, making it an effective
/// choice for maintaining data locality.
///
/// [`store`]: ContiguousMemory::store
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct ContiguousMemory<S: MemoryImpl = ImplDefault> {
    inner: S::State,
}

/// Internal state of [`ContiguousMemory`].
pub struct ContiguousMemoryState<S: MemoryImpl = ImplDefault> {
    base: S::Base,
    size: S::SizeType,
    alignment: usize,
    tracker: S::AllocationTracker,
}

impl Clone for ContiguousMemoryState<ImplFixed> {
    fn clone(&self) -> Self {
        Self {
            base: self.base,
            size: self.size,
            alignment: self.alignment,
            tracker: self.tracker.clone(),
        }
    }
}

impl<S: MemoryImpl> core::ops::Deref for ContiguousMemory<S> {
    type Target = ContiguousMemoryState<S>;

    fn deref(&self) -> &Self::Target {
        S::deref_state(&self.inner)
    }
}

impl<S: MemoryImpl> ContiguousMemoryState<S> {
    /// Returns the layout of the memory managed by the [`ContiguousMemory`]
    pub fn layout(&self) -> Layout {
        unsafe {
            let capacity = S::get_capacity(core::mem::transmute(self));
            Layout::from_size_align_unchecked(capacity, self.alignment)
        }
    }
}

impl<S: MemoryImpl> ContiguousMemory<S> {
    /// Creates a new `ContiguousMemory` instance with the specified capacity.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The initial capacity of the memory container.
    ///
    /// # Returns
    ///
    /// A `Result` containing the newly created `ContiguousMemory` instance on
    /// success, or a `LayoutError` if the memory layout cannot be satisfied.
    pub fn new(capacity: usize) -> Self {
        Self::new_aligned(capacity, 1)
            .expect("unable to create a ContiguousMemory with alignment of 1")
    }

    /// Creates a new `ContiguousMemory` instance with the specified capacity
    /// and alignment.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The initial capacity of the memory container.
    /// * `alignment` - The alignment requirement for memory allocations.
    ///
    /// # Returns
    ///
    /// A `Result` containing the newly created `ContiguousMemory` instance on
    /// success, or a `LayoutError` if the memory layout cannot be satisfied.
    pub fn new_aligned(capacity: usize, alignment: usize) -> Result<Self, LayoutError> {
        let layout = Layout::from_size_align(capacity, alignment)?;
        let base = unsafe { allocator::alloc(layout) };
        Ok(ContiguousMemory {
            inner: S::build_state(base, capacity, alignment)?,
        })
    }

    /// Retrieves the base address of the allocated memory.
    ///
    /// # Safety
    ///
    /// This function is marked as unsafe because it returns a raw pointer to
    /// the allocated memory.
    ///
    /// # Returns
    ///
    /// - If the implementation details type `S` is
    ///   [`ImplConcurrent`], the result will be a
    ///   `Result<*mut u8, [LockingError](crate::LockingError::Poisoned)>` which
    ///   only errors if the mutex holding the base address fails.
    ///
    /// - For other implementation base address `*mut u8` is returned directly.
    pub unsafe fn get_base(&self) -> S::LockResult<*mut u8> {
        S::get_base(&self.inner)
    }

    /// Returns the current capacity of the memory container.
    ///
    /// The capacity represents the size of the memory block that has been
    /// allocated for storing data. It may be larger than the amount of data
    /// currently stored within the container.
    pub fn get_capacity(&self) -> usize {
        S::get_capacity(&self.inner)
    }

    /// Resizes the memory container to the specified capacity.
    ///
    /// This function can either grow or shrink the container based on the new
    /// capacity.
    ///
    /// # Arguments
    ///
    /// * `new_capacity` - The desired new capacity of the memory container.
    ///
    /// # Returns
    ///
    /// A `Result` indicating success on resizing the container, or a
    /// `ContiguousMemoryError` if an error occurs.
    ///
    /// # Errors
    ///
    /// This function can return the following errors:
    ///
    /// - [`ContiguousMemoryError::Unshrinkable`]: This error occurs when
    ///   attempting to shrink the memory container, but the stored data
    ///   prevents the container from being shrunk to the desired capacity.
    ///
    /// - [`ContiguousMemoryError::Lock`]: This error can occur if the mutex
    ///   holding the base address or the [`AllocationTracker`] is poisoned.
    ///
    /// [`AllocationTracker`]: crate::tracker::AllocationTracker
    pub fn resize(&mut self, new_capacity: usize) -> Result<(), ContiguousMemoryError> {
        if new_capacity == S::get_capacity(&self.inner) {
            return Ok(());
        }

        let old_capacity = S::get_capacity(&self.inner);
        S::resize_tracker(&mut self.inner, new_capacity)?;
        match S::resize(&mut self.inner, new_capacity) {
            Ok(_) => {}
            Err(ContiguousMemoryError::Lock(lock_err)) if S::USE_LOCKS => {
                S::resize_tracker(&mut self.inner, old_capacity)?;
                return Err(ContiguousMemoryError::Lock(lock_err));
            }
            Err(other) => return Err(other),
        }

        Ok(())
    }

    pub fn shrink_to_fit(&mut self) -> Result<(), ContiguousMemoryError> {
        if let Some(shrunk) = S::shrink_tracker(&mut self.inner)? {
            self.resize(shrunk)?;
        }
        Ok(())
    }

    /// Stores a value of type `T` in the memory container.
    ///
    /// This operation allocates memory for the provided value and stores it in
    /// the contiguous memory block.
    ///
    /// # Arguments
    ///
    /// * `value` - The value of type `T` to be stored in the memory container.
    ///
    /// # Returns
    ///
    /// - If the implementation details are [`ImplDefault`] the result will be
    ///   a [`ContiguousMemoryRef`] pointing to the stored value.
    ///
    ///
    /// A `Result` that encapsulates the result of the storage operation:
    ///
    /// - If the implementation details are [`ImplConcurrent`], the result will
    ///   be a [`SyncContiguousMemoryRef`] pointing to the stored value.
    ///
    ///
    /// - If the implementation details are [`ImplFixed`], the result will be a
    ///   raw pointer (`*mut T`) to the stored value.
    ///
    /// The returned [`Result`] indicates success or an error if the storage
    /// operation encounters any issues.
    ///
    /// ## Errors
    ///
    /// When the implementation details are [`ImplConcurrent`]:
    ///
    /// - [`LockingError::Poisoned`]: This error can occur when the
    ///   [`AllocationTracker`] associated with the memory container is
    ///   poisoned.
    ///
    /// When the implementation details are [`ImplFixed`]:
    ///
    /// - [`ContiguousMemoryError::NoStorageLeft`]: Indicates that
    ///   the container couldn't accommodate the provided data due to size
    ///   limitations. Other implementation details grow the container instead.
    ///
    /// [`AllocationTracker`]: crate::tracker::AllocationTracker
    pub fn store<T: StoreRequirements>(&mut self, value: T) -> S::StoreResult<T>
    where
        Self: StoreData<S>,
    {
        let mut data = ManuallyDrop::new(value);
        let layout = Layout::for_value(&data);
        let pos = &mut *data as *mut T;
        let result = unsafe { self.store_data(pos, layout) };
        result
    }
}

/// Trait for specializing store function across implementations
pub trait StoreData<S: MemoryImpl> {
    /// Works same as [`store`](ContiguousMemory::store) but takes a pointer and layout
    unsafe fn store_data<T: StoreRequirements>(
        &mut self,
        data: *mut T,
        layout: Layout,
    ) -> S::StoreResult<T>;
}

impl StoreData<ImplConcurrent> for ContiguousMemory<ImplConcurrent> {
    /// # Errors
    ///
    /// [`LockingError::Poisoned`]: This error can occur when the
    /// [`AllocationTracker`] associated with the memory container is poisoned.
    ///
    /// [`AllocationTracker`]: crate::tracker::AllocationTracker
    unsafe fn store_data<T: StoreRequirements>(
        &mut self,
        data: *mut T,
        layout: Layout,
    ) -> Result<SyncContiguousMemoryRef<T>, LockingError> {
        let (addr, range) = loop {
            match ImplConcurrent::next_free(&mut self.inner, layout) {
                Ok(taken) => {
                    let found =
                        (taken.0 + ImplConcurrent::get_base(&self.inner)? as usize) as *mut u8;
                    unsafe { core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size()) }
                    break (found, taken);
                }
                Err(ContiguousMemoryError::NoStorageLeft) => {
                    match self.resize(ImplConcurrent::get_capacity(&self.inner) * 2) {
                        Ok(()) => {}
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

impl StoreData<ImplDefault> for ContiguousMemory<ImplDefault> {
    unsafe fn store_data<T: StoreRequirements>(
        &mut self,
        data: *mut T,
        layout: Layout,
    ) -> ContiguousMemoryRef<T> {
        let (addr, range) = loop {
            match ImplDefault::next_free(&mut self.inner, layout) {
                Ok(taken) => {
                    let found = (taken.0 + self.base.get() as usize) as *mut u8;
                    unsafe {
                        core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                    }
                    break (found, taken);
                }
                Err(ContiguousMemoryError::NoStorageLeft) => {
                    match self.resize(ImplDefault::get_capacity(&self.inner) * 2) {
                        Ok(()) => {},
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

impl StoreData<ImplFixed> for ContiguousMemory<ImplFixed> {
    unsafe fn store_data<T: StoreRequirements>(
        &mut self,
        data: *mut T,
        layout: Layout,
    ) -> Result<*mut T, ContiguousMemoryError> {
        let (addr, range) = loop {
            match ImplFixed::next_free(&mut self.inner, layout) {
                Ok(taken) => {
                    let found = (taken.0 + self.base as usize) as *mut u8;
                    unsafe {
                        core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                    }
                    break (found, taken);
                }
                Err(other) => return Err(other),
            }
        };

        Ok(ImplFixed::build_ref(&self.inner, addr as *mut T, &range))
    }
}

impl ContiguousMemory<ImplFixed> {
    #[inline(always)]
    pub unsafe fn free_typed<T>(&mut self, value: *mut T) {
        Self::free(self, value, size_of::<T>())
    }

    pub unsafe fn free<T>(&mut self, value: *mut T, size: usize) {
        let pos: usize = value.sub(self.get_base() as usize) as usize;
        if let Some(freed) = ImplFixed::free_region(&mut self.inner, ByteRange(pos, pos + size)) {
            core::ptr::drop_in_place(freed as *mut T);
        }
    }
}

/// A type alias for [`ContiguousMemory`] that enables
/// references to data stored within it to be used safely across multiple
/// threads.
pub type SyncContiguousMemory = ContiguousMemory<ImplConcurrent>;

/// A type alias for [`ContiguousMemory`] that offers
/// a synchronous implementation without using internal mutexes making it
/// faster but not thread safe.
pub type GrowableContiguousMemory = ContiguousMemory<ImplDefault>;

/// A type alias for [`ContiguousMemory`] that provides
/// a highly performance-optimized (unsafe) implementation. Suitable when the
/// required size is known upfront and the container is guaranteed to outlive
/// any returned pointers.
pub type FixedContiguousMemory = ContiguousMemory<ImplFixed>;

impl<S: MemoryImpl> Drop for ContiguousMemory<S> {
    fn drop(&mut self) {
        S::deallocate(&self.base, self.layout())
    }
}

/// A synchronized (thread-safe) reference to `T` data stored in a
/// [`ContiguousMemory`] structure.
pub struct SyncContiguousMemoryRef<T: ?Sized> {
    inner: Arc<ReferenceState<T, ImplConcurrent>>,
    #[cfg(feature = "ptr_metadata")]
    metadata: <T as Pointee>::Metadata,
    #[cfg(not(feature = "ptr_metadata"))]
    _phantom: PhantomData<T>,
}

/// A shorter type name for [`SyncContiguousMemoryRef`].
pub type SCMRef<T> = SyncContiguousMemoryRef<T>;

impl<T: ?Sized> SyncContiguousMemoryRef<T> {
    /// Tries accessing referenced data at its current location.
    ///
    /// # Errors
    ///
    /// This function returns
    /// [`LockingError::Poisoned`](crate::error::LockingError::Poisoned) error
    /// if the Mutex holding the `base` address pointer has been poisoned.
    pub fn get(&self) -> Result<&T, LockingError>
    where
        T: RefSizeReq,
    {
        unsafe {
            let base = ImplConcurrent::get_base(&self.inner.state)?;
            let pos = base.add(self.inner.range.0);

            #[cfg(not(feature = "ptr_metadata"))]
            {
                Ok(&*(pos as *mut T))
            }
            #[cfg(feature = "ptr_metadata")]
            {
                Ok(&*core::ptr::from_raw_parts(pos as *const (), self.metadata))
            }
        }
    }

    /// Tries accessing referenced data at its current location and hangs the
    /// current thread if the referenced data is already mutably borrowed.
    ///
    /// # Errors
    ///
    /// This function can return the following errors:
    ///
    /// - [`LockingError::Poisoned`] error if the Mutex holding the base address
    ///   pointer or the Mutex holding concurrent mutable access flag has been
    ///   poisoned.
    pub fn get_mut<'a>(&'a self) -> Result<MemWriteGuard<'a, T, ImplConcurrent>, LockingError>
    where
        T: RefSizeReq,
    {
        let read = self
            .inner
            .already_borrowed
            .lock_named(error::MutexKind::Reference)?;
        unsafe {
            let base = ImplConcurrent::get_base(&self.inner.state)?;
            let pos = base.add(self.inner.range.0);
            Ok(MemWriteGuard {
                state: self.inner.clone(),
                _guard: read,
                #[cfg(not(feature = "ptr_metadata"))]
                value: &mut *(pos as *mut T),
                #[cfg(feature = "ptr_metadata")]
                value: &mut *core::ptr::from_raw_parts_mut::<T>(pos as *mut (), self.metadata),
            })
        }
    }

    /// Tries accessing referenced data at its current location.
    ///
    /// # Errors
    ///
    /// This function can return the following errors:
    ///
    /// - [`LockingError::Poisoned`] error if the Mutex holding the base address
    ///   pointer or the Mutex holding mutable access exclusion flag has been
    ///   poisoned.
    ///
    /// - [`LockingError::WouldBlock`] error if accessing referenced data chunk
    ///   would be blocking.
    pub fn try_get_mut<'a>(&'a self) -> Result<MemWriteGuard<'a, T, ImplConcurrent>, LockingError>
    where
        T: RefSizeReq,
    {
        let read = self
            .inner
            .already_borrowed
            .try_lock_named(error::MutexKind::Reference)?;
        unsafe {
            let base = ImplConcurrent::get_base(&self.inner.state)?;
            let pos = base.add(self.inner.range.0);
            Ok(MemWriteGuard {
                state: self.inner.clone(),
                _guard: read,
                #[cfg(not(feature = "ptr_metadata"))]
                value: &mut *(pos as *mut T),
                #[cfg(feature = "ptr_metadata")]
                value: &mut *core::ptr::from_raw_parts_mut::<T>(pos as *mut (), self.metadata),
            })
        }
    }

    #[cfg(feature = "ptr_metadata")]
    pub fn as_dyn<R: ?Sized>(self, metadata: <R as Pointee>::Metadata) -> SyncContiguousMemoryRef<R>
    where
        T: Unsize<R>,
    {
        unsafe {
            SyncContiguousMemoryRef {
                inner: core::mem::transmute(self.inner),
                metadata,
            }
        }
    }
}

impl<T: ?Sized> Clone for SyncContiguousMemoryRef<T> {
    fn clone(&self) -> Self {
        SyncContiguousMemoryRef {
            inner: self.inner.clone(),
            #[cfg(feature = "ptr_metadata")]
            metadata: self.metadata.clone(),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }
}

/// A thread-unsafe reference to `T` data stored in [`ContiguousMemory`]
/// structure.
pub struct ContiguousMemoryRef<T: ?Sized> {
    inner: Rc<ReferenceState<T, ImplDefault>>,
    #[cfg(feature = "ptr_metadata")]
    metadata: <T as Pointee>::Metadata,
    #[cfg(not(feature = "ptr_metadata"))]
    _phantom: PhantomData<T>,
}
/// A shorter type name for [`ContiguousMemoryRef`].
pub type CMRef<T> = ContiguousMemoryRef<T>;

impl<T: ?Sized> ContiguousMemoryRef<T> {
    /// Returns a reference to data at its current location.
    pub fn get(&self) -> &T
    where
        T: RefSizeReq,
    {
        ContiguousMemoryRef::<T>::try_get(self).expect("mutably borrowed")
    }

    /// Returns a reference to data at its current location.
    pub fn try_get(&self) -> Result<&T, MutablyBorrowed>
    where
        T: RefSizeReq,
    {
        if self.inner.already_borrowed.get() {
            return Err(MutablyBorrowed {
                range: self.inner.range,
            });
        }

        unsafe {
            let base = ImplDefault::get_base(&self.inner.state);
            let pos = base.add(self.inner.range.0);

            #[cfg(not(feature = "ptr_metadata"))]
            {
                Ok(&*(pos as *mut T))
            }
            #[cfg(feature = "ptr_metadata")]
            {
                Ok(&*core::ptr::from_raw_parts(pos as *const (), self.metadata))
            }
        }
    }

    /// Returns a mutable reference to data at its current location or the
    /// [`MutablyBorrowed`] error if the represented memory region is already
    /// mutably borrowed.
    pub fn get_mut<'a>(&'a mut self) -> MemWriteGuard<'a, T, ImplDefault>
    where
        T: RefSizeReq,
    {
        ContiguousMemoryRef::<T>::try_get_mut(self).expect("mutably borrowed")
    }

    /// Returns a mutable reference to data at its current location or the
    /// [`MutablyBorrowed`] error if the represented memory region is already
    /// mutably borrowed.
    pub fn try_get_mut<'a>(
        &'a mut self,
    ) -> Result<MemWriteGuard<'a, T, ImplDefault>, MutablyBorrowed>
    where
        T: RefSizeReq,
    {
        if self.inner.already_borrowed.get() {
            return Err(MutablyBorrowed {
                range: self.inner.range,
            });
        }

        unsafe {
            let base = ImplDefault::get_base(&self.inner.state);
            let pos = base.add(self.inner.range.0);

            Ok(MemWriteGuard {
                state: self.inner.clone(),
                _guard: (),
                #[cfg(not(feature = "ptr_metadata"))]
                value: &mut *(pos as *mut T),
                #[cfg(feature = "ptr_metadata")]
                value: &mut *core::ptr::from_raw_parts_mut::<T>(pos as *mut (), self.metadata),
            })
        }
    }

    #[cfg(feature = "ptr_metadata")]
    pub fn as_dyn<R: ?Sized>(self, metadata: <R as Pointee>::Metadata) -> ContiguousMemoryRef<R>
    where
        T: Unsize<R>,
    {
        unsafe {
            ContiguousMemoryRef {
                inner: core::mem::transmute(self.inner),
                metadata,
            }
        }
    }
}

impl<T: ?Sized> Clone for ContiguousMemoryRef<T> {
    fn clone(&self) -> Self {
        ContiguousMemoryRef {
            inner: self.inner.clone(),
            #[cfg(feature = "ptr_metadata")]
            metadata: self.metadata.clone(),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }
}

impl<T: ?Sized> core::ops::Deref for ContiguousMemoryRef<T>
where
    T: RefSizeReq,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.get()
    }
}

/// Internal state of [`ContiguousMemoryRef`] and [`SyncContiguousMemoryRef`].
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct ReferenceState<T: ?Sized, S: ReferenceImpl = ImplDefault> {
    state: S::MemoryState,
    range: ByteRange,
    already_borrowed: S::RefMutLock,
    #[cfg(feature = "ptr_metadata")]
    drop_metadata: DynMetadata<dyn HandleDrop>,
    _phantom: PhantomData<T>,
}

impl<T: ?Sized, S: ReferenceImpl> Drop for ReferenceState<T, S> {
    fn drop(&mut self) {
        #[allow(unused_variables)]
        if let Some(it) = S::free_region(&mut self.state, self.range) {
            #[cfg(feature = "ptr_metadata")]
            unsafe {
                let drop: *mut dyn HandleDrop =
                    core::ptr::from_raw_parts_mut::<dyn HandleDrop>(it, self.drop_metadata);
                (&*drop).do_drop();
            }
        };
    }
}

/// A smart reference wrapper responsible for tracking and managing a flag
/// that indicates whether the memory segment is actively being written to.
pub struct MemWriteGuard<'a, T: ?Sized, S: ReferenceImpl> {
    state: S::RefState<T>,
    _guard: S::RefMutGuard<'a>,
    value: &'a mut T,
}

impl<'a, T: ?Sized, S: ReferenceImpl> core::ops::Deref for MemWriteGuard<'a, T, S> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized, S: ReferenceImpl> DerefMut for MemWriteGuard<'a, T, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized, S: ReferenceImpl> Drop for MemWriteGuard<'a, T, S> {
    fn drop(&mut self) {
        S::unborrow_ref::<T>(&self.state);
    }
}

#[cfg(all(test, feature = "std"))]
mod test {
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
    fn test_new_contiguous_memory() {
        let memory = GrowableContiguousMemory::new(1024);
        assert_eq!(memory.get_capacity(), 1024);
    }

    #[test]
    fn test_store_and_get_contiguous_memory() {
        let mut memory = GrowableContiguousMemory::new(1024);

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

        assert_eq!(*stored_ref_number, value_number);
        assert_eq!(*stored_ref_car_a, car_a);
        assert_eq!(*stored_ref_string, value_string);
        assert_eq!(*stored_ref_car_b, car_b);
        assert_eq!(*stored_ref_byte, value_byte);
    }

    #[test]
    fn test_resize_contiguous_memory() {
        let mut memory = GrowableContiguousMemory::new(512);

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

        assert_eq!(*stored_car, car_a);

        memory.resize(128).unwrap();
        assert_eq!(memory.get_capacity(), 128);

        assert_eq!(*stored_car, car_a);
    }

    #[test]
    fn test_fixed_contiguous_memory() {
        let mut memory = FixedContiguousMemory::new_aligned(1024, 8).unwrap();

        let value = 42u32;
        let stored_ref = memory.store(value).unwrap();
        unsafe {
            assert_eq!(*stored_ref, value);
        }

        // No resize allowed for FixedContiguousMemory
        assert!(memory.resize(2048).is_err());
    }
}
