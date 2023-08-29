#![cfg_attr(feature = "no_std", no_std)]
#![cfg_attr(feature = "ptr_metadata", feature(ptr_metadata))]
#![cfg_attr(feature = "error_in_core", feature(error_in_core))]

#[cfg(feature = "no_std")]
extern crate alloc;

#[cfg(any(
    all(not(feature = "std"), not(feature = "no_std")),
    all(feature = "std", feature = "no_std")
))]
compile_error!(
    "contiguous_mem requires either 'std' or 'no_std' feature to be enabled, not both or neither"
);

pub mod details;
pub mod error;
pub mod range;
pub mod tracker;
mod types;
mod util;

use details::*;
use range::ByteRange;
use types::*;

use core::{
    alloc::{Layout, LayoutError},
    mem::size_of,
    ops::DerefMut,
};

#[cfg(not(feature = "ptr_metadata"))]
use core::marker::PhantomData;

#[cfg(feature = "ptr_metadata")]
use core::ptr::Pointee;

use error::{BorrowMutError, ContiguousMemoryError, LockingError};

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
/// [`store`]: crate::details::ImplDetails::store
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct ContiguousMemory<S: MemoryImpl = ImplDefault> {
    inner: S::State,
}

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
    pub fn layout(&self) -> Layout {
        unsafe {
            let capacity = S::get_capacity(core::mem::transmute(self));
            Layout::from_size_align_unchecked(capacity, self.alignment)
        }
    }
}

impl<S: ImplDetails> ContiguousMemory<S> {
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
        let base = unsafe { alloc::alloc(layout) };
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
    ///   [`ThreadSafeImpl`](crate::ThreadSafeImpl), the result will be a
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
    /// - [`ContiguousMemoryError::Lock`]: This error can occur if the mutex
    ///   holding the base address or the
    ///   [`AllocationTracker`](crate::AllocationTracker) is poisoned.
    ///
    /// - [`ContiguousMemoryError::Unshrinkable`]: This error occurs when
    ///   attempting to shrink the memory container, but the stored data
    ///   prevents the container from being shrunk to the desired capacity.
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
    /// A `Result` that encapsulates the result of the storage operation:
    ///
    /// - If the implementation details type `S` is
    ///   [`NotThreadSafeImpl`](crate::NotThreadSafeImpl) or
    ///   [`ThreadSafeImpl`](crate::ThreadSafeImpl), the result will be a
    ///   [`crate::CMRef`] pointing to the stored value. This reference provides
    ///   a convenient and safe way to access and manipulate the stored data
    ///   within the memory block.
    ///
    /// - If the implementation details type `S` is
    ///   [`FixedSizeImpl`](crate::FixedSizeImpl), the result will be a raw
    ///   pointer (`*mut T`) to the stored value. This is due to the fact that
    ///   fixed-size container won't move which means the pointer will not be
    ///   invalidated.
    ///
    /// The returned [`Result`] indicates success or an error if the storage
    /// operation encounters any issues.
    ///
    /// # Errors
    ///
    /// This function can return the following errors:
    ///
    /// - [`ContiguousMemoryError::NoStorageLeft`]: Only returned when the
    ///   implementation details type `S` is
    ///   [`FixedSizeImpl`](crate::FixedSizeImpl) and indicates that the
    ///   container couldn't accommodate the provided data due to size
    ///   limitations. Other implementation details grow the container instead.
    ///
    /// - [`ContiguousMemoryError::Poisoned`]: This error can occur when the
    ///   [`AllocationTracker`](crate::AllocationTracker) associated with the
    ///   memory container is poisoned.
    pub fn store<T>(&mut self, mut value: T) -> Result<S::Type<T>, ContiguousMemoryError>
    where
        Self: StoreData<S>,
    {
        let layout = Layout::for_value(&value);
        let pos: *mut T = &mut value;
        unsafe {
            self.store_data(pos as *mut u8, layout)
                .map(|it| S::cast(it))
        }
    }
}

/// Trait for specializing store function across implementations
pub trait StoreData<S: ReferenceImpl> {
    /// Works same as [`store`](CanStore::store) but takes a pointer and layout
    unsafe fn store_data(
        &mut self,
        data: *mut u8,
        layout: Layout,
    ) -> Result<S::Type<u8>, ContiguousMemoryError>;
}

impl StoreData<ImplConcurrent> for ContiguousMemory<ImplConcurrent> {
    unsafe fn store_data(
        &mut self,
        data: *mut u8,
        layout: Layout,
    ) -> Result<SyncContiguousMemoryRef<u8>, ContiguousMemoryError> {
        let (addr, range) = loop {
            match ImplConcurrent::next_free(&mut self.inner, layout) {
                Ok(taken) => {
                    let found =
                        (taken.0 + ImplConcurrent::get_base(&self.inner)? as usize) as *mut u8;
                    unsafe { core::ptr::copy_nonoverlapping(data, found, layout.size()) }
                    break (found, taken);
                }
                Err(ContiguousMemoryError::NoStorageLeft) => {
                    self.resize(ImplConcurrent::get_capacity(&self.inner) * 2)?;
                }
                Err(other) => return Err(other),
            }
        };

        Ok(ImplConcurrent::build_ref(&self.inner, addr, &range))
    }
}

impl StoreData<ImplDefault> for ContiguousMemory<ImplDefault> {
    unsafe fn store_data(
        &mut self,
        data: *mut u8,
        layout: Layout,
    ) -> Result<ContiguousMemoryRef<u8>, ContiguousMemoryError> {
        let (addr, range) = loop {
            match ImplDefault::next_free(&mut self.inner, layout) {
                Ok(taken) => {
                    let found = (taken.0 + self.base.get() as usize) as *mut u8;
                    unsafe {
                        core::ptr::copy_nonoverlapping(data, found, layout.size());
                    }
                    break (found, taken);
                }
                Err(ContiguousMemoryError::NoStorageLeft) => {
                    self.resize(ImplDefault::get_capacity(&self.inner) * 2)?;
                }
                Err(other) => return Err(other),
            }
        };

        Ok(ImplDefault::build_ref(&self.inner, addr, &range))
    }
}

impl StoreData<ImplFixed> for ContiguousMemory<ImplFixed> {
    unsafe fn store_data(
        &mut self,
        data: *mut u8,
        layout: Layout,
    ) -> Result<*mut u8, ContiguousMemoryError> {
        let (addr, range) = loop {
            match ImplFixed::next_free(&mut self.inner, layout) {
                Ok(taken) => {
                    let found = (taken.0 + self.base as usize) as *mut u8;
                    unsafe {
                        core::ptr::copy_nonoverlapping(data, found, layout.size());
                    }
                    break (found, taken);
                }
                Err(other) => return Err(other),
            }
        };

        Ok(ImplFixed::build_ref(&self.inner, addr, &range))
    }
}

impl ContiguousMemory<ImplFixed> {
    #[inline(always)]
    pub unsafe fn free_typed<T>(&mut self, value: *mut T) -> Result<(), ContiguousMemoryError> {
        Self::free(self, value, size_of::<T>())
    }

    pub unsafe fn free<T>(
        &mut self,
        value: *mut T,
        size: usize,
    ) -> Result<(), ContiguousMemoryError> {
        ImplFixed::release_reference(
            &mut self.inner,
            ByteRange(value as usize, value as usize + size),
        )
    }
}

/// A type alias for [`ContiguousMemory`](crate::ContiguousMemory) that enables
/// references to data stored within it to be used safely across multiple
/// threads.
pub type SyncContiguousMemory = ContiguousMemory<ImplConcurrent>;

/// A type alias for [`ContiguousMemory`](crate::ContiguousMemory) that offers
/// a synchronous implementation without using internal mutexes making it
/// faster but not thread safe.
pub type GrowableContiguousMemory = ContiguousMemory<ImplDefault>;

/// A type alias for [`ContiguousMemory`](crate::ContiguousMemory) that provides
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
    inner: Arc<ReferenceState<ImplConcurrent>>,
    #[cfg(feature = "ptr_metadata")]
    metadata: <T as Pointee>::Metadata,
    #[cfg(not(feature = "ptr_metadata"))]
    _phantom: PhantomData<T>,
}

/// A shorter type name for [`AsyncContiguousMemoryRef`].
pub type ACMRef<T> = SyncContiguousMemoryRef<T>;

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
        T: Sized,
    {
        unsafe {
            let base = ImplConcurrent::get_base(&self.inner.state)?;
            let pos = base.offset(self.inner.range.0 as isize);
            Ok(&*(pos as *mut T))
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
        T: Sized,
    {
        let read = self
            .inner
            .mutable_access
            .lock_named(error::MutexKind::Reference)?;
        unsafe {
            let base = ImplConcurrent::get_base(&self.inner.state)?;
            let pos = base.offset(self.inner.range.0 as isize);
            Ok(MemWriteGuard {
                state: self.inner.clone(),
                _guard: read,
                value: &mut *(pos as *mut T),
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
        T: Sized,
    {
        let read = self
            .inner
            .mutable_access
            .try_lock_named(error::MutexKind::Reference)?;
        unsafe {
            let base = ImplConcurrent::get_base(&self.inner.state)?;
            let pos = base.offset(self.inner.range.0 as isize);
            Ok(MemWriteGuard {
                state: self.inner.clone(),
                _guard: read,
                value: &mut *(pos as *mut T),
            })
        }
    }

    pub unsafe fn cast<R: ?Sized>(self) -> SyncContiguousMemoryRef<R> {
        SyncContiguousMemoryRef {
            inner: self.inner,
            _phantom: PhantomData,
        }
    }
}

impl<T: ?Sized> Clone for SyncContiguousMemoryRef<T> {
    fn clone(&self) -> Self {
        SyncContiguousMemoryRef {
            inner: self.inner.clone(),
            #[cfg(feature = "ptr_metadata")]
            metadata: self.metadata.clone(),
            _phantom: PhantomData,
        }
    }
}

/// A thread-unsafe reference to `T` data stored in [`ContiguousMemory`]
/// structure.
pub struct ContiguousMemoryRef<T: ?Sized> {
    inner: Rc<ReferenceState<ImplDefault>>,
    metadata: Option<VTableAddr>,
    _phantom: PhantomData<T>,
}
/// A shorter type name for [`ContiguousMemoryRef`].
pub type CMRef<T> = ContiguousMemoryRef<T>;

impl<T: Sized> ContiguousMemoryRef<T> {
    /// Returns a reference to data at its current location.
    pub fn get(&self) -> &T {
        unsafe {
            let base = ImplDefault::get_base(&self.inner.state);
            let pos = base.offset(self.inner.range.0 as isize);
            &*(pos as *mut T)
        }
    }

    /// Returns a mutable reference to data at its current location or the
    /// [`BorrowMutError`] error if the represented memory region is already
    /// mutably borrowed.
    pub fn get_mut<'a>(&'a mut self) -> MemWriteGuard<'a, T, ImplDefault> {
        ContiguousMemoryRef::<T>::try_get_mut(self).expect("already borrowed")
    }

    /// Returns a mutable reference to data at its current location or the
    /// [`BorrowMutError`] error if the represented memory region is already
    /// mutably borrowed.
    pub fn try_get_mut<'a>(
        &'a mut self,
    ) -> Result<MemWriteGuard<'a, T, ImplDefault>, BorrowMutError> {
        if !self.inner.mutable_access.get() {
            return Err(BorrowMutError {
                range: self.inner.range,
            });
        }
        unsafe {
            let base = ImplDefault::get_base(&self.inner.state);
            let pos = base.offset(self.inner.range.0 as isize);
            Ok(MemWriteGuard {
                state: self.inner.clone(),
                _guard: (),
                value: &mut *(pos as *mut T),
            })
        }
    }

    pub unsafe fn as_dyn<R: ?Sized>(self, vtable: VTableAddr) -> ContiguousMemoryRef<R> {
        ContiguousMemoryRef {
            inner: self.inner,
            metadata: Some(vtable),
            _phantom: PhantomData,
        }
    }
}

/*
impl<T: ?Sized> ContiguousMemoryRef<T> {
    pub fn get_dyn(&self) -> &T {
        unsafe {
            let base = ImplDefault::get_base(&self.inner.state);
            let pos = base.offset(self.inner.range.0 as isize) as *const ();
            let metadata = self.metadata.expect("missing metadata");
            let dynamic: *const T = core::mem::transmute((pos, metadata));
            &*dynamic
        }
    }
}
*/

impl<T: ?Sized> Clone for ContiguousMemoryRef<T> {
    fn clone(&self) -> Self {
        ContiguousMemoryRef {
            inner: self.inner.clone(),
            metadata: self.metadata.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<T> core::ops::Deref for ContiguousMemoryRef<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.get()
    }
}

/// Internal state of [`ContiguousMemoryRef`] and [`AsyncContiguousMemoryRef`].
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct ReferenceState<S: ReferenceImpl = ImplDefault> {
    state: S::MemoryState,
    range: ByteRange,
    mutable_access: S::RefMutLock,
}

impl<S: ReferenceImpl> Drop for ReferenceState<S> {
    fn drop(&mut self) {
        let _ = S::release_reference(&mut self.state, self.range);
    }
}

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

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct VTableAddr(usize);

impl VTableAddr {
    pub unsafe fn new(value: usize) -> Self {
        VTableAddr(value)
    }
}

#[macro_export]
macro_rules! vtable {
    ($struct: ty as $trait: tt) => {
        unsafe {
            let value: *const $struct = core::ptr::null();
            let dynamic: *const dyn $trait = value as *const dyn $trait;
            let (_, addr) = core::mem::transmute::<_, (*const (), usize)>(dynamic);
            ::contiguous_mem::VTableAddr::new(addr)
        }
    };
}

/* TODO: Reference getters
#[cfg(not(feature = "ptr_metadata"))]
impl<T: Sized, S: ImplDetails> ReferenceState<T, S> {
    pub fn get(&self) -> Result<&T, ContiguousMemoryError> {
        unsafe {
            let base = S::get_base(&self.base)?.offset(self.range.0 as isize);
            Ok(&*(base as *mut T))
        }
    }
}

#[cfg(feature = "ptr_metadata")]
impl<T: ?Sized, S: ImplDetails> ReferenceState<T, S> {
    pub fn get(&self) -> Result<&T, ContiguousMemoryError> {
        unsafe {
            let base = S::get_base(&self.base)?.offset(self.range.0 as isize);
            let fat: *const T = core::ptr::from_raw_parts::<T>(base as *const (), self.metadata);
            Ok(&*fat)
        }
    }
}
 */

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_new_contiguous_memory() {
        let memory = ContiguousMemory::<ImplDefault>::new_aligned(1024, 8).unwrap();
        assert_eq!(memory.get_capacity(), 1024);
    }

    #[test]
    fn test_store_and_get_contiguous_memory() {
        let mut memory = ContiguousMemory::<ImplDefault>::new_aligned(1024, 8).unwrap();

        let value = 42u32;
        let stored_ref = memory.store(value).unwrap();
        assert_eq!(*stored_ref, value);
    }

    #[test]
    fn test_resize_contiguous_memory() {
        let mut memory = ContiguousMemory::<ImplDefault>::new_aligned(1024, 8).unwrap();

        memory.resize(512).unwrap();
        assert_eq!(memory.get_capacity(), 512);

        memory.resize(2048).unwrap();
        assert_eq!(memory.get_capacity(), 2048);
    }

    #[test]
    fn test_growable_contiguous_memory() {
        let mut memory = GrowableContiguousMemory::new_aligned(1024, 8).unwrap();

        let value = 42u32;
        let stored_ref = memory.store(value).unwrap();
        assert_eq!(*stored_ref, value);

        memory.resize(2048).unwrap();
        assert_eq!(memory.get_capacity(), 2048);
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

    struct TestStruct1 {
        field1: u32,
        field2: u64,
    }

    struct TestStruct2 {
        field1: u16,
        field2: f32,
        field3: i32,
    }

    #[test]
    fn test_store_structs_with_different_layouts() {
        let mut memory = ContiguousMemory::<ImplDefault>::new_aligned(1024, 8).unwrap();

        let struct1 = TestStruct1 {
            field1: 42,
            field2: 1234567890,
        };
        let struct2 = TestStruct2 {
            field1: 123,
            field2: 3.14,
            field3: -42,
        };

        let stored_struct1 = memory.store(struct1).unwrap();
        let stored_struct2 = memory.store(struct2).unwrap();

        assert_eq!(stored_struct1.field1, 42);
        assert_eq!(stored_struct1.field2, 1234567890);

        assert_eq!(stored_struct2.field1, 123);
        assert_eq!(stored_struct2.field2, 3.14);
        assert_eq!(stored_struct2.field3, -42);
    }
}
