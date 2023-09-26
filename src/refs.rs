//! Returned reference types and read/write guards.
//!
//! See [`ContiguousMemoryStorage::push`](crate::ContiguousMemory::push)
//! for information on implementation specific return values.

use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use crate::{
    common::*, error::RegionBorrowError, memory::ManageMemory, range::ByteRange, types::*,
};

#[cfg(feature = "sync_impl")]
use crate::common::ImplConcurrent;
#[cfg(feature = "sync_impl")]
use crate::error::{LockTarget, LockingError};
#[cfg(feature = "ptr_metadata")]
use core::marker::Unsize;
#[cfg(feature = "ptr_metadata")]
use core::ptr::Pointee;

/// A synchronized (thread-safe) reference to `T` data stored in a
/// [`ContiguousMemoryStorage`](crate::ContiguousMemory) structure.
#[cfg(feature = "sync_impl")]
pub struct SyncContiguousEntryRef<T: ?Sized, A: ManageMemory> {
    pub(crate) inner: Arc<ReferenceState<T, ImplConcurrent, A>>,
    #[cfg(feature = "ptr_metadata")]
    pub(crate) metadata: <T as Pointee>::Metadata,
    #[cfg(not(feature = "ptr_metadata"))]
    pub(crate) _phantom: PhantomData<T>,
}

/// A shorter type name for [`SyncContiguousEntryRef`].
#[cfg(feature = "sync_impl")]
pub type SCERef<T, A> = SyncContiguousEntryRef<T, A>;

#[cfg(feature = "sync_impl")]
impl<T: ?Sized, A: ManageMemory> SyncContiguousEntryRef<T, A> {
    /// Returns a byte range within container memory this reference points to.
    pub fn range(&self) -> ByteRange {
        self.inner.range
    }

    /// Returns a reference to data at its current location or returns a
    /// [`LockingError::Poisoned`] error if the Mutex holding the `base` address
    /// pointer has been poisoned.
    ///
    /// If the data is mutably accessed, this method will block the current
    /// thread until it becomes available.
    pub fn get(&self) -> Result<MemoryReadGuard<'_, T, ImplConcurrent, A>, LockingError>
    where
        T: RefSizeReq,
    {
        let guard = self.inner.borrow_kind.read_named(LockTarget::Reference)?;

        unsafe {
            let base = <ImplConcurrent as ImplDetails<A>>::get_base(&self.inner.state.base)?;
            let pos = self.inner.range.offset_base_unwrap(base);

            Ok(MemoryReadGuard {
                state: self.inner.clone(),
                guard,
                #[cfg(not(feature = "ptr_metadata"))]
                value: &*(pos),
                #[cfg(feature = "ptr_metadata")]
                value: &*core::ptr::from_raw_parts(pos, self.metadata),
            })
        }
    }

    /// Returns a reference to data at its current location or returns a
    /// [`LockingError::Poisoned`] error if the Mutex holding the `base` address
    /// pointer has been poisoned.
    ///
    /// If the data is mutably accessed, this method returns a
    /// [`LockingError::WouldBlock`] error.
    pub fn try_get(&self) -> Result<MemoryReadGuard<'_, T, ImplConcurrent, A>, LockingError>
    where
        T: RefSizeReq,
    {
        let guard = self
            .inner
            .borrow_kind
            .try_read_named(LockTarget::Reference)?;

        unsafe {
            let base = <ImplConcurrent as ImplDetails<A>>::get_base(&self.inner.state.base)?;
            let pos = self.inner.range.offset_base_unwrap(base);

            Ok(MemoryReadGuard {
                state: self.inner.clone(),
                guard,
                #[cfg(not(feature = "ptr_metadata"))]
                value: &*(pos),
                #[cfg(feature = "ptr_metadata")]
                value: &*core::ptr::from_raw_parts(pos, self.metadata),
            })
        }
    }

    /// Returns or write guard to referenced data at its current location a
    /// [`LockingError::Poisoned`] error if the Mutex holding the base address
    /// pointer or the Mutex holding concurrent mutable access flag has been
    /// poisoned.
    pub fn get_mut(&mut self) -> Result<MemoryWriteGuard<'_, T, ImplConcurrent, A>, LockingError>
    where
        T: RefSizeReq,
    {
        let guard = self.inner.borrow_kind.write_named(LockTarget::Reference)?;
        unsafe {
            let base = <ImplConcurrent as ImplDetails<A>>::get_base(&self.inner.state.base)?;
            let pos = self.inner.range.offset_base_unwrap(base);

            Ok(MemoryWriteGuard {
                state: self.inner.clone(),
                guard,
                #[cfg(not(feature = "ptr_metadata"))]
                value: &mut *(pos),
                #[cfg(feature = "ptr_metadata")]
                value: &mut *core::ptr::from_raw_parts_mut::<T>(pos, self.metadata),
            })
        }
    }

    /// Returns a write guard to referenced data at its current location or a
    /// `LockingError` if that isn't possible.
    ///
    /// # Errors
    ///
    /// This function can return the following errors:
    ///
    /// * [`LockingError::Poisoned`] error if the Mutex holding the base address
    ///   pointer or the Mutex holding mutable access exclusion flag has been
    ///   poisoned.
    ///
    /// * [`LockingError::WouldBlock`] error if accessing referenced data chunk
    ///   would be blocking.
    pub fn try_get_mut(
        &mut self,
    ) -> Result<MemoryWriteGuard<'_, T, ImplConcurrent, A>, LockingError>
    where
        T: RefSizeReq,
    {
        let guard = self
            .inner
            .borrow_kind
            .try_write_named(LockTarget::Reference)?;
        unsafe {
            let base =
                <ImplConcurrent as ImplReferencing<A>>::try_get_base(&self.inner.state.base)?;
            let pos = self.inner.range.offset_base_unwrap(base);

            Ok(MemoryWriteGuard {
                state: self.inner.clone(),
                guard,
                #[cfg(not(feature = "ptr_metadata"))]
                value: &mut *(pos),
                #[cfg(feature = "ptr_metadata")]
                value: &mut *core::ptr::from_raw_parts_mut::<T>(pos, self.metadata),
            })
        }
    }

    /// Casts this reference into a dynamic type `R`.
    #[cfg(feature = "ptr_metadata")]
    pub fn into_dyn<R: ?Sized>(self) -> SyncContiguousEntryRef<R>
    where
        T: Sized + Unsize<R>,
    {
        unsafe {
            SyncContiguousEntryRef {
                inner: core::mem::transmute(self.inner),
                metadata: static_metadata::<T, R>(),
            }
        }
    }

    /// Tries downcasting this dynamic reference into a discrete type `R`,
    /// returns None if `R` drop handler doesn't match the original one.
    #[cfg(feature = "ptr_metadata")]
    pub fn downcast_dyn<R: Unsize<T>>(self) -> Option<SyncContiguousEntryRef<R>> {
        if self.inner.drop_fn != drop_fn::<R>() {
            return None;
        }
        unsafe {
            Some(SyncContiguousEntryRef {
                inner: core::mem::transmute(self.inner),
                metadata: (),
            })
        }
    }

    /// Transmutes this reference to type `R` with provided `metadata`.
    ///
    /// [`static_metadata`](crate::static_metadata) function may be used to
    /// statically construct metadata for a struct-trait pair.
    ///
    /// # Safety
    ///
    /// See: [`ContiguousEntryRef::with_metadata`]
    #[cfg(feature = "ptr_metadata")]
    pub unsafe fn with_metadata<R: ?Sized>(
        self,
        metadata: <R as Pointee>::Metadata,
    ) -> SyncContiguousEntryRef<R> {
        unsafe {
            SyncContiguousEntryRef {
                inner: core::mem::transmute(self.inner),
                metadata,
            }
        }
    }

    /// Creates an immutable pointer to underlying data, blocking the current
    /// thread until base address can be read.
    ///
    /// This function can return a [`LockingError::Poisoned`] error if the Mutex
    /// holding the base address pointer has been poisoned.
    ///
    /// # Safety
    ///
    /// See: [`ContiguousEntryRef::as_ptr`]
    pub unsafe fn as_ptr(&self) -> Result<*const T, LockingError>
    where
        T: RefSizeReq,
    {
        self.as_ptr_mut().map(|it| it as *const T)
    }

    /// Creates a mutable pointer to underlying data, blocking the current
    /// thread until base address can be read.
    ///
    /// This function can return a [`LockingError::Poisoned`] error if the Mutex
    /// holding the base address pointer has been poisoned.
    ///
    /// # Safety
    ///
    /// See: [`ContiguousEntryRef::as_ptr_mut`]
    pub unsafe fn as_ptr_mut(&self) -> Result<*mut T, LockingError>
    where
        T: RefSizeReq,
    {
        let base = <ImplConcurrent as ImplDetails<A>>::get_base(&self.inner.state.base)?;
        let pos = self.inner.range.offset_base_unwrap(base);
        #[cfg(not(feature = "ptr_metadata"))]
        {
            Ok(pos)
        }
        #[cfg(feature = "ptr_metadata")]
        {
            Ok(core::ptr::from_raw_parts_mut::<T>(pos, self.metadata))
        }
    }

    /// Creates an immutable pointer to underlying data while also preventing
    /// the occupied memory region from being marked as free, blocking the
    /// current thread until base address can be read
    ///
    /// This function can return a [`LockingError::Poisoned`] error if the Mutex
    /// holding the base address pointer has been poisoned.
    ///
    /// # Safety
    ///
    /// See: [`ContiguousEntryRef::into_ptr`]
    pub unsafe fn into_ptr(self) -> Result<*const T, LockingError>
    where
        T: RefSizeReq,
    {
        self.into_ptr_mut().map(|it| it as *const T)
    }

    /// Creates a mutable pointer to underlying data while also preventing
    /// the occupied memory region from being marked as free, blocking the
    /// current thread until base address can be read
    ///
    /// This function can return a [`LockingError::Poisoned`] error if the Mutex
    /// holding the base address pointer has been poisoned.
    ///
    /// # Safety
    ///
    /// See: [`ContiguousEntryRef::into_ptr_mut`]
    pub unsafe fn into_ptr_mut(self) -> Result<*mut T, LockingError>
    where
        T: RefSizeReq,
    {
        let result = self.as_ptr_mut();
        let inner: *mut ReferenceState<T, ImplConcurrent, A> = self.inner.as_ref()
            as *const ReferenceState<T, ImplConcurrent, A>
            as *mut ReferenceState<T, ImplConcurrent, A>;
        core::ptr::drop_in_place(&mut (*inner).state);
        core::mem::forget(self.inner);
        result
    }
}

#[cfg(feature = "sync_impl")]
impl<T: ?Sized, A: ManageMemory> Clone for SyncContiguousEntryRef<T, A> {
    fn clone(&self) -> Self {
        SyncContiguousEntryRef {
            inner: self.inner.clone(),
            #[cfg(feature = "ptr_metadata")]
            metadata: self.metadata,
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }
}

#[cfg(feature = "debug")]
impl<T: ?Sized, A: ManageMemory> core::fmt::Debug for SyncContiguousEntryRef<T, A> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SyncContiguousEntryRef")
            .field("inner", &self.inner)
            .finish()
    }
}

/// A thread-unsafe reference to `T` data stored in
/// [`ContiguousMemoryStorage`](crate::ContiguousMemory) structure.
pub struct ContiguousEntryRef<T: ?Sized, A: ManageMemory> {
    pub(crate) inner: Rc<ReferenceState<T, ImplDefault, A>>,
    #[cfg(feature = "ptr_metadata")]
    pub(crate) metadata: <T as Pointee>::Metadata,
    #[cfg(not(feature = "ptr_metadata"))]
    pub(crate) _phantom: PhantomData<T>,
}

/// A shorter type name for [`ContiguousEntryRef`].
pub type CERef<T, A> = ContiguousEntryRef<T, A>;

impl<T: ?Sized, A: ManageMemory> ContiguousEntryRef<T, A> {
    /// Returns a byte range within container memory this reference points to.
    pub fn range(&self) -> ByteRange {
        self.inner.range
    }

    /// Returns a reference to data at its current location and panics if the
    /// represented memory region is mutably borrowed.
    pub fn get(&self) -> MemoryReadGuard<'_, T, ImplDefault, A>
    where
        T: RefSizeReq,
    {
        ContiguousEntryRef::<T, A>::try_get(self).expect("mutably borrowed")
    }

    /// Returns a reference to data at its current location or a
    /// [`RegionBorrowError`] error if the represented memory region is
    /// mutably borrowed.
    pub fn try_get(&self) -> Result<MemoryReadGuard<'_, T, ImplDefault, A>, RegionBorrowError>
    where
        T: RefSizeReq,
    {
        let state = self.inner.borrow_kind.get();
        if let BorrowState::Read(count) = state {
            self.inner.borrow_kind.set(BorrowState::Read(count + 1));
        } else {
            return Err(RegionBorrowError {
                range: self.inner.range,
            });
        }

        unsafe {
            let base = <ImplDefault as ImplDetails<A>>::get_base(&self.inner.state.base);
            let pos = self.inner.range.offset_base_unwrap(base);

            Ok(MemoryReadGuard {
                state: self.inner.clone(),
                #[cfg(feature = "sync_impl")]
                guard: (),
                #[cfg(not(feature = "ptr_metadata"))]
                value: &*(pos),
                #[cfg(feature = "ptr_metadata")]
                value: &*core::ptr::from_raw_parts_mut::<T>(pos, self.metadata),
            })
        }
    }

    /// Returns a mutable reference to data at its current location and panics
    /// if the reference has already been borrowed.
    pub fn get_mut(&mut self) -> MemoryWriteGuard<'_, T, ImplDefault, A>
    where
        T: RefSizeReq,
    {
        ContiguousEntryRef::<T, A>::try_get_mut(self).expect("mutably borrowed")
    }

    /// Returns a mutable reference to data at its current location or a
    /// [`RegionBorrowError`] error if the represented memory region is
    /// already borrowed.
    pub fn try_get_mut(
        &mut self,
    ) -> Result<MemoryWriteGuard<'_, T, ImplDefault, A>, RegionBorrowError>
    where
        T: RefSizeReq,
    {
        if self.inner.borrow_kind.get() != BorrowState::Read(0) {
            return Err(RegionBorrowError {
                range: self.inner.range,
            });
        } else {
            self.inner.borrow_kind.set(BorrowState::Write);
        }

        unsafe {
            let base = <ImplDefault as ImplDetails<A>>::get_base(&self.inner.state.base);
            let pos = self.inner.range.offset_base_unwrap(base);

            Ok(MemoryWriteGuard {
                state: self.inner.clone(),
                #[cfg(feature = "sync_impl")]
                guard: (),
                #[cfg(not(feature = "ptr_metadata"))]
                value: &mut *(pos),
                #[cfg(feature = "ptr_metadata")]
                value: &mut *core::ptr::from_raw_parts_mut::<T>(pos, self.metadata),
            })
        }
    }

    /// Casts this reference into a dynamic type `R`.
    #[cfg(feature = "ptr_metadata")]
    pub fn into_dyn<R: ?Sized>(self) -> ContiguousEntryRef<R>
    where
        T: Sized + Unsize<R>,
    {
        unsafe {
            ContiguousEntryRef {
                inner: core::mem::transmute(self.inner),
                metadata: static_metadata::<T, R>(),
            }
        }
    }

    /// Tries downcasting this dynamic reference into a discrete type `R`,
    /// returns None if `R` drop handler doesn't match the original one.
    #[cfg(feature = "ptr_metadata")]
    pub fn downcast_dyn<R: Unsize<T>>(self) -> Option<ContiguousEntryRef<R>> {
        if self.inner.drop_fn != drop_fn::<R>() {
            return None;
        }
        unsafe {
            Some(ContiguousEntryRef {
                inner: core::mem::transmute(self.inner),
                metadata: (),
            })
        }
    }

    /// Transmutes this reference to type `R` with provided `metadata`.
    ///
    /// [`static_metadata`](crate::static_metadata) function may be used to
    /// statically construct metadata for a struct-trait pair.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it assumes any `T` to implement `R`,
    /// as the original type of stored data can be erased through
    /// [`into_dyn`](ContiguousEntryRef::into_dyn) it's impossible to check
    /// whether the initial struct actually implements `R`.
    ///
    /// Calling methods from an incorrect vtable will cause undefined behavior.
    #[cfg(feature = "ptr_metadata")]
    pub unsafe fn with_metadata<R: ?Sized>(
        self,
        metadata: <R as Pointee>::Metadata,
    ) -> ContiguousEntryRef<R> {
        unsafe {
            ContiguousEntryRef {
                inner: core::mem::transmute(self.inner),
                metadata,
            }
        }
    }

    /// Creates an immutable pointer to underlying data.
    ///
    /// # Safety
    ///
    /// This function returns a pointer that may become invalid if the
    /// container's memory is resized to a capacity which requires the memory
    /// segment to be moved.
    ///
    /// When the reference goes out of scope, its region will be marked as free
    /// which means that a subsequent call to [`ContiguousMemoryStorage::push`]
    /// or friends can cause undefined behavior when dereferencing the pointer.
    ///
    /// [`ContiguousMemoryStorage::push`]: crate::ContiguousMemory::push
    pub unsafe fn as_ptr(&self) -> *const T
    where
        T: RefSizeReq,
    {
        self.as_ptr_mut() as *const T
    }

    /// Creates a mutable pointer to underlying data.
    ///
    /// # Safety
    ///
    /// In addition to concerns noted in [`ContiguousEntryRef::as_ptr`],
    /// this function also provides mutable access to the underlying data
    /// allowing potential data races.
    pub unsafe fn as_ptr_mut(&self) -> *mut T
    where
        T: RefSizeReq,
    {
        let base = <ImplDefault as ImplDetails<A>>::get_base(&self.inner.state.base);
        let pos = self.inner.range.offset_base_unwrap(base);

        #[cfg(not(feature = "ptr_metadata"))]
        {
            pos
        }
        #[cfg(feature = "ptr_metadata")]
        {
            core::ptr::from_raw_parts_mut::<T>(pos, self.metadata)
        }
    }

    /// Creates an immutable pointer to underlying data while also preventing
    /// the occupied memory region from being marked as free.
    ///
    /// # Safety
    ///
    /// This function returns a pointer that may become invalid if the
    /// container's memory is resized to a capacity which requires the memory
    /// segment to be moved.
    pub unsafe fn into_ptr(self) -> *const T
    where
        T: RefSizeReq,
    {
        self.into_ptr_mut() as *const T
    }

    /// Creates a mutable pointer to underlying data while also preventing
    /// the occupied memory region from being marked as free.
    ///
    /// # Safety
    ///
    /// In addition to concerns noted in
    /// [`ContiguousEntryRef::into_ptr`], this function also provides
    /// mutable access to the underlying data allowing potential data races.
    pub unsafe fn into_ptr_mut(self) -> *mut T
    where
        T: RefSizeReq,
    {
        let result = self.as_ptr_mut();
        let inner: *mut ReferenceState<T, ImplDefault, A> = self.inner.as_ref()
            as *const ReferenceState<T, ImplDefault, A>
            as *mut ReferenceState<T, ImplDefault, A>;
        core::ptr::drop_in_place(&mut (*inner).state);
        core::mem::forget(self.inner);
        result
    }
}

impl<T: ?Sized, A: ManageMemory> Clone for ContiguousEntryRef<T, A> {
    fn clone(&self) -> Self {
        ContiguousEntryRef {
            inner: self.inner.clone(),
            #[cfg(feature = "ptr_metadata")]
            metadata: self.metadata,
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }
}

#[cfg(feature = "debug")]
impl<T: ?Sized, A: ManageMemory> core::fmt::Debug for ContiguousEntryRef<T, A> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ContiguousEntryRef")
            .field("inner", &self.inner)
            .finish()
    }
}

pub(crate) mod sealed {
    use crate::memory::ManageMemory;

    use super::*;

    /// Internal state of [`ContiguousEntryRef`] and [`SyncContiguousEntryRef`].
    pub struct ReferenceState<T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> {
        pub state: Impl::StorageState,
        pub range: ByteRange,
        pub borrow_kind: Impl::BorrowLock,
        pub drop_fn: DropFn,
        pub _phantom: PhantomData<T>,
    }

    #[cfg(feature = "debug")]
    impl<T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> core::fmt::Debug
        for ReferenceState<T, Impl, A>
    where
        Impl::StorageState: core::fmt::Debug,
        Impl::BorrowLock: core::fmt::Debug,
    {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.debug_struct("ReferenceState")
                .field("state", &self.state)
                .field("range", &self.range)
                .field("borrow_kind", &self.borrow_kind)
                .finish()
        }
    }

    impl<T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> Drop for ReferenceState<T, Impl, A> {
        fn drop(&mut self) {
            let base = Impl::get_base(&self.state.base);
            let tracker = Impl::get_allocation_tracker(&mut self.state);
            if let Some(it) = Impl::free_region(tracker, base, self.range) {
                (self.drop_fn)(it);
            };
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum BorrowKind {
        Read,
        Write,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum BorrowState {
        Read(usize),
        Write,
    }

    /// Size requirements for types pointed to by references
    #[cfg(feature = "ptr_metadata")]
    pub trait RefSizeReq {}
    #[cfg(feature = "ptr_metadata")]
    impl<T: ?Sized> RefSizeReq for T {}

    /// Size requirements for types pointed to by references
    #[cfg(not(feature = "ptr_metadata"))]
    pub trait RefSizeReq: Sized {}
    #[cfg(not(feature = "ptr_metadata"))]
    impl<T: Sized> RefSizeReq for T {}
}
use sealed::*;

/// A smart reference wrapper responsible for tracking and managing a flag
/// that indicates whether the memory segment is actively being written to.
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct MemoryWriteGuard<'a, T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> {
    state: Impl::RefState<T>,
    #[allow(unused)]
    #[cfg(feature = "sync_impl")]
    guard: Impl::WriteGuard<'a>,
    value: &'a mut T,
}

impl<'a, T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> Deref
    for MemoryWriteGuard<'a, T, Impl, A>
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> DerefMut
    for MemoryWriteGuard<'a, T, Impl, A>
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> Drop
    for MemoryWriteGuard<'a, T, Impl, A>
{
    fn drop(&mut self) {
        Impl::unborrow_ref::<T>(&self.state, BorrowKind::Write);
    }
}

/// A smart reference wrapper responsible for tracking and managing a flag
/// that indicates whether the memory segment is actively being read from.
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct MemoryReadGuard<'a, T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> {
    state: Impl::RefState<T>,
    #[allow(unused)]
    #[cfg(feature = "sync_impl")]
    guard: Impl::ReadGuard<'a>,
    value: &'a T,
}

impl<'a, T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> Deref
    for MemoryReadGuard<'a, T, Impl, A>
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> Drop
    for MemoryReadGuard<'a, T, Impl, A>
{
    fn drop(&mut self) {
        Impl::unborrow_ref::<T>(&self.state, BorrowKind::Read);
    }
}
