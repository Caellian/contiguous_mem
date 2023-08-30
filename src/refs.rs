use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use crate::{
    details::{ImplConcurrent, ImplDefault, MemoryImpl, ReferenceImpl},
    error::{LockingError, MutablyBorrowed, MutexKind},
    range::ByteRange,
    types::*,
};

/// A synchronized (thread-safe) reference to `T` data stored in a
/// [`ContiguousMemory`] structure.
pub struct SyncContiguousMemoryRef<T: ?Sized> {
    pub(crate) inner: Arc<ReferenceState<T, ImplConcurrent>>,
    #[cfg(feature = "ptr_metadata")]
    pub(crate) metadata: <T as Pointee>::Metadata,
    #[cfg(not(feature = "ptr_metadata"))]
    pub(crate) _phantom: PhantomData<T>,
}

/// A shorter type name for [`SyncContiguousMemoryRef`].
pub type SCMRef<T> = SyncContiguousMemoryRef<T>;

impl<T: ?Sized> SyncContiguousMemoryRef<T> {
    /// Returns a byte range within container memory.
    pub fn range(&self) -> ByteRange {
        self.inner.range
    }

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
            .lock_named(MutexKind::Reference)?;
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
            .try_lock_named(MutexKind::Reference)?;
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
    pub fn into_dyn<R: ?Sized>(self) -> SyncContiguousMemoryRef<R>
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

/// A thread-unsafe reference to `T` data stored in [`ContiguousMemory`]
/// structure.
pub struct ContiguousMemoryRef<T: ?Sized> {
    pub(crate) inner: Rc<ReferenceState<T, ImplDefault>>,
    #[cfg(feature = "ptr_metadata")]
    pub(crate) metadata: <T as Pointee>::Metadata,
    #[cfg(not(feature = "ptr_metadata"))]
    pub(crate) _phantom: PhantomData<T>,
}
/// A shorter type name for [`ContiguousMemoryRef`].
pub type CMRef<T> = ContiguousMemoryRef<T>;

impl<T: ?Sized> ContiguousMemoryRef<T> {
    /// Returns a byte range within container memory.
    pub fn range(&self) -> ByteRange {
        self.inner.range
    }

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
    pub fn into_dyn<R: ?Sized>(self) -> ContiguousMemoryRef<R>
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

impl<T: ?Sized> Deref for ContiguousMemoryRef<T>
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
    pub(crate) state: S::MemoryState,
    pub(crate) range: ByteRange,
    pub(crate) already_borrowed: S::RefMutLock,
    #[cfg(feature = "ptr_metadata")]
    pub(crate) drop_metadata: DynMetadata<dyn HandleDrop>,
    pub(crate) _phantom: PhantomData<T>,
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

impl<'a, T: ?Sized, S: ReferenceImpl> Deref for MemWriteGuard<'a, T, S> {
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
