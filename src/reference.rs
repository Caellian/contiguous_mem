//! Returned reference types and read/write guards.
//!
//! See [`ContiguousMemoryStorage::push`](crate::ContiguousMemory::push)
//! for information on implementation specific return values.

use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::{null, null_mut},
};

use crate::{
    error::RegionBorrowError, memory::ManageMemory, range::ByteRange, raw::MemoryState, types::*,
};

#[cfg(feature = "ptr_metadata")]
use core::marker::Unsize;
#[cfg(feature = "ptr_metadata")]
use core::ptr::Pointee;

/// A reference to an entry of type `T` stored in
/// [`ContiguousMemoryStorage`](crate::ContiguousMemory).
pub struct EntryRef<T: ?Sized, A: ManageMemory, Impl: ImplReferencing<A> = ImplDefault> {
    pub(crate) inner: Impl::SharedRef<ReferenceState<T, Impl, A>>,
    #[cfg(feature = "ptr_metadata")]
    pub(crate) metadata: <T as Pointee>::Metadata,
}

/// A shorter type name for [`EntryRef`].
pub type CERef<T, A, Impl> = EntryRef<T, A, Impl>;

impl<T: ?Sized, A: ManageMemory, Impl: ImplReferencing<A>> EntryRef<T, A, Impl> {
    /// Returns a byte range within container memory this reference points to.
    pub fn range(&self) -> ByteRange {
        self.inner.range
    }

    #[inline]
    fn get_impl(&self) -> Result<MemoryReadGuard<'_, T, A, Impl>, RegionBorrowError>
    where
        T: RefSizeReq,
    {
        let mut borrow = WritableInner::write(&self.inner.borrow_kind).unwrap();
        if let BorrowState::Read(count) = *borrow {
            *borrow = BorrowState::Read(count + 1);
        } else {
            return Err(RegionBorrowError {
                range: self.inner.range,
                borrow_state: *borrow,
            });
        }

        let base = ReadableInner::read(&self.inner.state.base).unwrap();
        unsafe {
            let pos = base.as_ptr().add(self.inner.range.0);

            Ok(MemoryReadGuard {
                state: self.inner.clone(),
                #[cfg(not(feature = "ptr_metadata"))]
                value: &*pos,
                #[cfg(feature = "ptr_metadata")]
                value: &*core::ptr::from_raw_parts::<T>(pos as *const (), self.metadata),
            })
        }
    }

    /// Returns a reference to data at its current location and panics if the
    /// represented memory region is mutably borrowed.
    pub fn get(&self) -> MemoryReadGuard<'_, T, A, Impl>
    where
        T: RefSizeReq,
    {
        match Self::get_impl(self) {
            Ok(it) => it,
            Err(RegionBorrowError { range, .. }) => {
                panic!("region {} already mutably borrowed", range)
            }
        }
    }

    /// Returns a reference to data at its current location or a
    /// [`RegionBorrowError`] error if the represented memory region is
    /// mutably borrowed.
    pub fn try_get(&self) -> Result<MemoryReadGuard<'_, T, A, Impl>, RegionBorrowError>
    where
        T: RefSizeReq,
    {
        Self::get_impl(self)
    }

    #[inline]
    fn get_mut_impl(&self) -> Result<MemoryWriteGuard<'_, T, A, Impl>, RegionBorrowError>
    where
        T: RefSizeReq,
    {
        let mut borrow = WritableInner::write(&self.inner.borrow_kind).unwrap();
        if *borrow != BorrowState::Read(0) {
            return Err(RegionBorrowError {
                range: self.inner.range,
                borrow_state: *borrow,
            });
        } else {
            *borrow = BorrowState::Write;
        }

        let base = ReadableInner::read(&self.inner.state.base).unwrap();
        unsafe {
            let pos = base.as_ptr().add(self.inner.range.0);

            Ok(MemoryWriteGuard {
                state: self.inner.clone(),
                #[cfg(not(feature = "ptr_metadata"))]
                value: &mut *(pos),
                #[cfg(feature = "ptr_metadata")]
                value: &mut *core::ptr::from_raw_parts_mut::<T>(pos as *mut (), self.metadata),
            })
        }
    }

    /// Returns a mutable reference to data at its current location and panics
    /// if the reference has already been borrowed.
    pub fn get_mut(&mut self) -> MemoryWriteGuard<'_, T, A, Impl>
    where
        T: RefSizeReq,
    {
        match Self::get_mut_impl(self) {
            Ok(it) => it,
            Err(RegionBorrowError { range, .. }) => {
                panic!("region {} already immutably borrowed", range)
            }
        }
    }

    /// Returns a mutable reference to data at its current location or a
    /// [`RegionBorrowError`] error if the represented memory region is
    /// already borrowed.
    pub fn try_get_mut(&mut self) -> Result<MemoryWriteGuard<'_, T, A, Impl>, RegionBorrowError>
    where
        T: RefSizeReq,
    {
        Self::get_mut_impl(self)
    }

    /// Casts this reference into a dynamic type `R`.
    #[cfg(feature = "ptr_metadata")]
    pub fn into_dyn<R: ?Sized>(self) -> EntryRef<R, A, Impl>
    where
        T: Sized + Unsize<R>,
    {
        // TODO: See if equal size can be guaranteed somehow and use transmute
        // for ptr_metadata casts

        EntryRef {
            inner: unsafe {
                // SAFETY: Reinterpretation of T to R is safe because both EntryRefs
                // are equally sized bc T is phantom. As A and Impl of the result
                // are the same, and Unsize requirement is satisfied, this pointer
                // cast is safe.
                //
                // Transform would be used, but it can't see the types are equally
                // sized due to use of type arguments.
                std::ptr::read(
                    &self.inner as *const Impl::SharedRef<ReferenceState<T, Impl, A>>
                        as *const Impl::SharedRef<ReferenceState<R, Impl, A>>,
                )
            },
            metadata: static_metadata::<T, R>(),
        }
    }

    /// Tries downcasting this dynamic reference into a discrete type `R`,
    /// returns None if `R` drop handler doesn't match the original one.
    #[cfg(feature = "ptr_metadata")]
    pub fn downcast_dyn<R: Unsize<T>>(self) -> Option<EntryRef<R, A, Impl>> {
        if self.inner.drop_fn != drop_fn::<R>() {
            return None;
        }
        Some(EntryRef {
            inner: unsafe {
                // SAFETY: See EntryRef::into_dyn
                std::ptr::read(
                    &self.inner as *const Impl::SharedRef<ReferenceState<T, Impl, A>>
                        as *const Impl::SharedRef<ReferenceState<R, Impl, A>>,
                )
            },
            metadata: (),
        })
    }

    /// Transmutes this reference to type `R` with provided `metadata`.
    ///
    /// [`static_metadata`] function may be used to statically construct
    /// metadata for a struct-trait pair.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it assumes any `T` to implement `R`,
    /// as the original type of stored data can be erased through
    /// [`into_dyn`](EntryRef::into_dyn) it's impossible to check
    /// whether the initial struct actually implements `R`.
    ///
    /// Calling methods from an incorrect vtable will cause undefined behavior.
    #[cfg(feature = "ptr_metadata")]
    pub unsafe fn with_metadata<R: ?Sized>(
        self,
        metadata: <R as Pointee>::Metadata,
    ) -> EntryRef<R, A, Impl> {
        EntryRef {
            inner: unsafe {
                // SAFETY: See EntryRef::into_dyn
                std::ptr::read(
                    &self.inner as *const Impl::SharedRef<ReferenceState<T, Impl, A>>
                        as *const Impl::SharedRef<ReferenceState<R, Impl, A>>,
                )
            },
            metadata,
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
    /// In addition to concerns noted in [`EntryRef::as_ptr`],
    /// this function also provides mutable access to the underlying data
    /// allowing potential data races.
    pub unsafe fn as_ptr_mut(&self) -> *mut T
    where
        T: RefSizeReq,
    {
        let base = ReadableInner::read(&self.inner.state.base).expect("unable to read base");
        let pos = base.as_ptr_mut().add(self.inner.range.0);

        #[cfg(not(feature = "ptr_metadata"))]
        {
            pos
        }
        #[cfg(feature = "ptr_metadata")]
        {
            core::ptr::from_raw_parts_mut::<T>(pos as *mut (), self.metadata)
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
    /// [`EntryRef::into_ptr`], this function also provides
    /// mutable access to the underlying data allowing potential data races.
    pub unsafe fn into_ptr_mut(self) -> *mut T
    where
        T: RefSizeReq,
    {
        let result = self.as_ptr_mut();
        let inner: *mut ReferenceState<T, Impl, A> = self.inner.deref()
            as *const ReferenceState<T, Impl, A>
            as *mut ReferenceState<T, Impl, A>;
        core::ptr::drop_in_place(&mut (*inner).state);
        core::mem::forget(self.inner);
        result
    }
}

impl<T: ?Sized, A: ManageMemory> Clone for EntryRef<T, A> {
    fn clone(&self) -> Self {
        EntryRef {
            inner: self.inner.clone(),
            #[cfg(feature = "ptr_metadata")]
            metadata: self.metadata,
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }
}

#[cfg(feature = "debug")]
impl<T: ?Sized, A: ManageMemory> core::fmt::Debug for EntryRef<T, A>
where
    MemoryState<ImplDefault, A>: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("EntryRef")
            .field("inner", &self.inner)
            .finish()
    }
}

pub(crate) mod state {
    use crate::{memory::ManageMemory, raw::MemoryState};

    use super::*;

    /// Internal state of [`EntryRef`].
    pub struct ReferenceState<T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> {
        pub state: Impl::StateRef<MemoryState<Impl, A>>,
        pub range: ByteRange,
        pub borrow_kind: Impl::BorrowLock,
        pub drop_fn: DropFn,
        pub _phantom: PhantomData<T>,
    }

    #[cfg(feature = "debug")]
    impl<T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> core::fmt::Debug
        for ReferenceState<T, Impl, A>
    where
        Impl::StateRef<MemoryState<Impl, A>>: core::fmt::Debug,
        Impl::BorrowLock: core::fmt::Debug,
    {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.debug_struct("EntryRef")
                .field("state", &self.state)
                .field("range", &self.range)
                .field("borrow_kind", &self.borrow_kind)
                .finish()
        }
    }

    impl<T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> Drop for ReferenceState<T, Impl, A> {
        fn drop(&mut self) {
            if let Ok(base) = ReadableInner::read(&self.state.base) {
                if let Ok(mut tracker) = WritableInner::write(&self.state.tracker) {
                    tracker.release(self.range);
                    unsafe { (self.drop_fn)(self.range.offset_base_unwrap(base.address)) };
                }
            }
        }
    }
}
use state::*;

/// Used for modelling XOR borrow semantics at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BorrowState {
    Read(usize),
    Write,
}

/// Size requirements for types pointed to by references
///
/// This is a sealed marker trait that allows `ptr_metadata` to control
/// whether Reference
#[cfg(feature = "ptr_metadata")]
pub trait RefSizeReq: Sealed {}
#[cfg(feature = "ptr_metadata")]
impl<T: ?Sized + Sealed> RefSizeReq for T {}

/// Size requirements for types pointed to by references
#[cfg(not(feature = "ptr_metadata"))]
pub trait RefSizeReq: Sized + Sealed {}
#[cfg(not(feature = "ptr_metadata"))]
impl<T: Sized + Sealed> RefSizeReq for T {}

/// Strategy for [`EntryRef`] construction when items are pushed into the
/// container.
pub trait ConstructReference<T, A: ManageMemory, Impl: ImplDetails<A> = ImplDefault>:
    Sized + Clone
{
    /// Constructs a result reference type specified by the
    /// [`implementation`](ImplDetails).
    ///
    /// Implementation of this method should be `#[inline]`d.
    fn new(state: &Impl::StateRef<MemoryState<Impl, A>>, range: ByteRange) -> Self;
}

impl<T, A: ManageMemory> ConstructReference<T, A, ImplDefault> for EntryRef<T, A> {
    #[inline]
    fn new(state: &Rc<MemoryState<ImplDefault, A>>, range: ByteRange) -> Self {
        EntryRef {
            inner: Reference::new(ReferenceState {
                state: state.clone(),
                range,
                borrow_kind: std::cell::Cell::new(BorrowState::Read(0)),
                drop_fn: drop_fn::<T>(),
                _phantom: PhantomData,
            }),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
        }
    }
}

#[cfg(feature = "unsafe_impl")]
impl<T, A: ManageMemory> ConstructReference<T, A, ImplUnsafe> for *mut T {
    #[inline]
    fn new(state: &Owned<MemoryState<ImplUnsafe, A>>, range: ByteRange) -> Self {
        if range.is_empty() {
            return null_mut();
        }
        unsafe {
            let base = ReadableInner::read(&state.base).unwrap();
            range.offset_base_unwrap(base.address)
        }
    }
}

/// A smart reference wrapper responsible for tracking and managing a flag
/// that indicates whether the memory segment is actively being written to.
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct MemoryWriteGuard<'a, T: ?Sized, A: ManageMemory, Impl: ImplReferencing<A> = ImplDefault>
{
    state: Impl::SharedRef<ReferenceState<T, Impl, A>>,
    #[allow(unused)]
    value: &'a mut T,
}

impl<'a, T: ?Sized, A: ManageMemory, Impl: ImplReferencing<A>> Deref
    for MemoryWriteGuard<'a, T, A, Impl>
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized, A: ManageMemory, Impl: ImplReferencing<A>> DerefMut
    for MemoryWriteGuard<'a, T, A, Impl>
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized, Impl: ImplReferencing<A>, A: ManageMemory> Drop
    for MemoryWriteGuard<'a, T, A, Impl>
{
    fn drop(&mut self) {
        Impl::unborrow_ref::<T>(&self.state);
    }
}

/// A smart reference wrapper responsible for tracking and managing a flag
/// that indicates whether the memory segment is actively being read from.
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct MemoryReadGuard<'a, T: ?Sized, A: ManageMemory, Impl: ImplReferencing<A> = ImplDefault> {
    state: Impl::SharedRef<ReferenceState<T, Impl, A>>,
    value: &'a T,
}

impl<'a, T: ?Sized, A: ManageMemory, Impl: ImplReferencing<A>> Deref
    for MemoryReadGuard<'a, T, A, Impl>
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized, A: ManageMemory, Impl: ImplReferencing<A>> Drop
    for MemoryReadGuard<'a, T, A, Impl>
{
    fn drop(&mut self) {
        Impl::unborrow_ref::<T>(&self.state);
    }
}
