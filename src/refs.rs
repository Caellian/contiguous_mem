//! Contains code relating to returned reference types and their internal state.
//!
//! Default implementation returns [`ContiguousMemoryRef`] when items are
//! stored which can be easily accessed through [`CMRef`] alias.
//!
//! Concurrent implementation returns [`SyncContiguousMemoryRef`] when items are
//! stored which can be easily accessed through [`SCMRef`] alias.

use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use crate::{
    details::{ImplConcurrent, ImplDefault, ImplDetails, StorageDetails},
    error::{LockSource, LockingError, RegionBorrowed},
    range::ByteRange,
    types::*,
};

/// Trait specifying interface of returned reference types.
pub trait ContiguousMemoryReference<T: ?Sized, Impl: ImplDetails> {
    /// Error type returned when the data represented by the reference can't be
    /// safely accessed/borrowed.
    type BorrowError;

    /// Returns a byte range within container memory this reference points to.
    fn range(&self) -> ByteRange;

    /// Returns a reference to data at its current location and panics if the
    /// reference has been mutably borrowed or blocks the thread for the
    /// concurrent implementation.
    fn get<'a>(&'a self) -> Impl::LockResult<MemoryReadGuard<'a, T, Impl>>
    where
        T: RefSizeReq;

    /// Returns a reference to data at its current location and returns the
    /// appropriate [error](Self::BorrowError) if that's not possible.
    fn try_get<'a>(&'a self) -> Result<MemoryReadGuard<'a, T, Impl>, Self::BorrowError>
    where
        T: RefSizeReq;

    /// Returns a mutable reference to data at its current location and panics
    /// if the reference has been mutably borrowed or blocks the thread for
    /// concurrent implementation.
    fn get_mut<'a>(&'a mut self) -> Impl::LockResult<MemoryWriteGuard<'a, T, Impl>>
    where
        T: RefSizeReq;

    /// Returns a mutable reference to data at its current location or an error
    /// [error](Self::BorrowError) if the represented memory region is already
    /// mutably borrowed.
    fn try_get_mut<'a>(&'a mut self) -> Result<MemoryWriteGuard<'a, T, Impl>, Self::BorrowError>
    where
        T: RefSizeReq;

    /// Casts this reference into a dynamic type `R`.
    #[cfg(feature = "ptr_metadata")]
    fn into_dyn<R: ?Sized>(self) -> Impl::ReferenceType<R>
    where
        T: Sized + Unsize<R>;
}

/// A synchronized (thread-safe) reference to `T` data stored in a
/// [`ContiguousMemoryStorage`](crate::ContiguousMemoryStorage) structure.
pub struct SyncContiguousMemoryRef<T: ?Sized> {
    pub(crate) inner: Arc<ReferenceState<T, ImplConcurrent>>,
    #[cfg(feature = "ptr_metadata")]
    pub(crate) metadata: <T as Pointee>::Metadata,
    #[cfg(not(feature = "ptr_metadata"))]
    pub(crate) _phantom: PhantomData<T>,
}

/// A shorter type name for [`SyncContiguousMemoryRef`].
pub type SCMRef<T> = SyncContiguousMemoryRef<T>;

impl<T: ?Sized> ContiguousMemoryReference<T, ImplConcurrent> for SyncContiguousMemoryRef<T> {
    type BorrowError = LockingError;

    fn range(&self) -> ByteRange {
        self.inner.range
    }

    /// Returns a reference to data at its current location or returns a
    /// [`LockingError::Poisoned`](crate::error::LockingError::Poisoned) error
    /// if the Mutex holding the `base` address pointer has been poisoned.
    ///
    /// If the data is mutably accessed, this method will block the current
    /// thread until it becomes available.
    fn get<'a>(&'a self) -> Result<MemoryReadGuard<'a, T, ImplConcurrent>, LockingError>
    where
        T: RefSizeReq,
    {
        let guard = self.inner.borrow_kind.read_named(LockSource::Reference)?;

        unsafe {
            let base = ImplConcurrent::get_base(&self.inner.state)?;
            let pos = base.add(self.inner.range.0);

            Ok(MemoryReadGuard {
                state: self.inner.clone(),
                guard,
                #[cfg(not(feature = "ptr_metadata"))]
                value: &*(pos as *mut T),
                #[cfg(feature = "ptr_metadata")]
                value: &*core::ptr::from_raw_parts(pos as *const (), self.metadata),
            })
        }
    }

    /// Returns a reference to data at its current location or returns a
    /// [`LockingError::Poisoned`](crate::error::LockingError::Poisoned) error
    /// if the Mutex holding the `base` address pointer has been poisoned.
    ///
    /// If the data is mutably accessed, this method return a
    /// [`LockingError::WouldBlock`](crate::error::LockingError::WouldBlock)
    /// error.
    fn try_get<'a>(&'a self) -> Result<MemoryReadGuard<'a, T, ImplConcurrent>, LockingError>
    where
        T: RefSizeReq,
    {
        let guard = self
            .inner
            .borrow_kind
            .try_read_named(LockSource::Reference)?;

        unsafe {
            let base = ImplConcurrent::get_base(&self.inner.state)?;
            let pos = base.add(self.inner.range.0);

            Ok(MemoryReadGuard {
                state: self.inner.clone(),
                guard,
                #[cfg(not(feature = "ptr_metadata"))]
                value: &*(pos as *mut T),
                #[cfg(feature = "ptr_metadata")]
                value: &*core::ptr::from_raw_parts(pos as *const (), self.metadata),
            })
        }
    }

    /// Returns or write guard to referenced data at its current location a
    /// [`LockingError::Poisoned`] error if the Mutex holding the base address
    /// pointer or the Mutex holding concurrent mutable access flag has been
    /// poisoned.
    fn get_mut<'a>(&'a mut self) -> Result<MemoryWriteGuard<'a, T, ImplConcurrent>, LockingError>
    where
        T: RefSizeReq,
    {
        let guard = self.inner.borrow_kind.write_named(LockSource::Reference)?;
        unsafe {
            let base = ImplConcurrent::get_base(&self.inner.state)?;
            let pos = base.add(self.inner.range.0);
            Ok(MemoryWriteGuard {
                state: self.inner.clone(),
                guard,
                #[cfg(not(feature = "ptr_metadata"))]
                value: &mut *(pos as *mut T),
                #[cfg(feature = "ptr_metadata")]
                value: &mut *core::ptr::from_raw_parts_mut::<T>(pos as *mut (), self.metadata),
            })
        }
    }

    /// Returns a write guard to referenced data at its current location or a
    /// `LockingError` if that isn't possible.
    ///
    /// This function can return the following errors:
    ///
    /// - [`LockingError::Poisoned`] error if the Mutex holding the base address
    ///   pointer or the Mutex holding mutable access exclusion flag has been
    ///   poisoned.
    ///
    /// - [`LockingError::WouldBlock`] error if accessing referenced data chunk
    ///   would be blocking.
    fn try_get_mut<'a>(
        &'a mut self,
    ) -> Result<MemoryWriteGuard<'a, T, ImplConcurrent>, LockingError>
    where
        T: RefSizeReq,
    {
        let guard = self
            .inner
            .borrow_kind
            .try_write_named(LockSource::Reference)?;
        unsafe {
            let base = ImplConcurrent::get_base(&self.inner.state)?;
            let pos = base.add(self.inner.range.0);
            Ok(MemoryWriteGuard {
                state: self.inner.clone(),
                guard,
                #[cfg(not(feature = "ptr_metadata"))]
                value: &mut *(pos as *mut T),
                #[cfg(feature = "ptr_metadata")]
                value: &mut *core::ptr::from_raw_parts_mut::<T>(pos as *mut (), self.metadata),
            })
        }
    }

    #[cfg(feature = "ptr_metadata")]
    fn into_dyn<R: ?Sized>(self) -> SyncContiguousMemoryRef<R>
    where
        T: Sized + Unsize<R>,
    {
        unsafe {
            SyncContiguousMemoryRef {
                inner: core::mem::transmute(self.inner),
                metadata: static_metadata::<T, R>(),
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

/// A thread-unsafe reference to `T` data stored in
/// [`ContiguousMemoryStorage`](crate::ContiguousMemoryStorage) structure.
pub struct ContiguousMemoryRef<T: ?Sized> {
    pub(crate) inner: Rc<ReferenceState<T, ImplDefault>>,
    #[cfg(feature = "ptr_metadata")]
    pub(crate) metadata: <T as Pointee>::Metadata,
    #[cfg(not(feature = "ptr_metadata"))]
    pub(crate) _phantom: PhantomData<T>,
}
/// A shorter type name for [`ContiguousMemoryRef`].
pub type CMRef<T> = ContiguousMemoryRef<T>;

impl<T: ?Sized> ContiguousMemoryReference<T, ImplDefault> for ContiguousMemoryRef<T> {
    type BorrowError = RegionBorrowed;

    fn range(&self) -> ByteRange {
        self.inner.range
    }

    fn get<'a>(&'a self) -> MemoryReadGuard<'a, T, ImplDefault>
    where
        T: RefSizeReq,
    {
        ContiguousMemoryRef::<T>::try_get(self).expect("mutably borrowed")
    }

    fn try_get<'a>(&'a self) -> Result<MemoryReadGuard<'a, T, ImplDefault>, RegionBorrowed>
    where
        T: RefSizeReq,
    {
        let state = self.inner.borrow_kind.get();
        if let BorrowState::Read(count) = state {
            self.inner.borrow_kind.set(BorrowState::Read(count + 1));
        } else {
            return Err(RegionBorrowed {
                range: self.inner.range,
            });
        }

        unsafe {
            let base = ImplDefault::get_base(&self.inner.state);
            let pos = base.add(self.inner.range.0);

            Ok(MemoryReadGuard {
                state: self.inner.clone(),
                guard: (),
                #[cfg(not(feature = "ptr_metadata"))]
                value: &*(pos as *mut T),
                #[cfg(feature = "ptr_metadata")]
                value: &*core::ptr::from_raw_parts_mut::<T>(pos as *mut (), self.metadata),
            })
        }
    }

    fn get_mut<'a>(&'a mut self) -> MemoryWriteGuard<'a, T, ImplDefault>
    where
        T: RefSizeReq,
    {
        ContiguousMemoryRef::<T>::try_get_mut(self).expect("mutably borrowed")
    }

    /// This implementation returns a [`RegionBorrowed`] error if the
    /// represented memory region is already borrowed.
    fn try_get_mut<'a>(&'a mut self) -> Result<MemoryWriteGuard<'a, T, ImplDefault>, RegionBorrowed>
    where
        T: RefSizeReq,
    {
        if self.inner.borrow_kind.get() != BorrowState::Read(0) {
            return Err(RegionBorrowed {
                range: self.inner.range,
            });
        } else {
            self.inner.borrow_kind.set(BorrowState::Write);
        }

        unsafe {
            let base = ImplDefault::get_base(&self.inner.state);
            let pos = base.add(self.inner.range.0);

            Ok(MemoryWriteGuard {
                state: self.inner.clone(),
                guard: (),
                #[cfg(not(feature = "ptr_metadata"))]
                value: &mut *(pos as *mut T),
                #[cfg(feature = "ptr_metadata")]
                value: &mut *core::ptr::from_raw_parts_mut::<T>(pos as *mut (), self.metadata),
            })
        }
    }

    #[cfg(feature = "ptr_metadata")]
    fn into_dyn<R: ?Sized>(self) -> ContiguousMemoryRef<R>
    where
        T: Sized + Unsize<R>,
    {
        unsafe {
            ContiguousMemoryRef {
                inner: core::mem::transmute(self.inner),
                metadata: static_metadata::<T, R>(),
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

pub(crate) mod sealed {
    use super::*;

    /// Internal state of [`ContiguousMemoryRef`] and [`SyncContiguousMemoryRef`].
    #[cfg_attr(feature = "debug", derive(Debug))]
    pub struct ReferenceState<T: ?Sized, Impl: ImplDetails> {
        pub state: Impl::StorageState,
        pub range: ByteRange,
        pub borrow_kind: Impl::BorrowLock,
        #[cfg(feature = "ptr_metadata")]
        pub drop_metadata: DynMetadata<dyn HandleDrop>,
        pub _phantom: PhantomData<T>,
    }

    impl<T: ?Sized, Impl: ImplDetails> Drop for ReferenceState<T, Impl> {
        fn drop(&mut self) {
            #[allow(unused_variables)]
            if let Some(it) = Impl::free_region(&mut self.state, self.range) {
                #[cfg(feature = "ptr_metadata")]
                unsafe {
                    let drop: *mut dyn HandleDrop =
                        core::ptr::from_raw_parts_mut::<dyn HandleDrop>(it, self.drop_metadata);
                    (&*drop).do_drop();
                }
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
}
use sealed::*;

/// A smart reference wrapper responsible for tracking and managing a flag
/// that indicates whether the memory segment is actively being written to.
pub struct MemoryWriteGuard<'a, T: ?Sized, Impl: ImplDetails> {
    state: Impl::RefState<T>,
    #[allow(unused)]
    guard: Impl::WriteGuard<'a>,
    value: &'a mut T,
}

impl<'a, T: ?Sized, Impl: ImplDetails> Deref for MemoryWriteGuard<'a, T, Impl> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized, Impl: ImplDetails> DerefMut for MemoryWriteGuard<'a, T, Impl> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized, Impl: ImplDetails> Drop for MemoryWriteGuard<'a, T, Impl> {
    fn drop(&mut self) {
        Impl::unborrow_ref::<T>(&self.state, BorrowKind::Write);
    }
}

/// A smart reference wrapper responsible for tracking and managing a flag
/// that indicates whether the memory segment is actively being read from.
pub struct MemoryReadGuard<'a, T: ?Sized, Impl: ImplDetails> {
    state: Impl::RefState<T>,
    #[allow(unused)]
    guard: Impl::ReadGuard<'a>,
    value: &'a T,
}

impl<'a, T: ?Sized, Impl: ImplDetails> Deref for MemoryReadGuard<'a, T, Impl> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized, Impl: ImplDetails> Drop for MemoryReadGuard<'a, T, Impl> {
    fn drop(&mut self) {
        Impl::unborrow_ref::<T>(&self.state, BorrowKind::Read);
    }
}
