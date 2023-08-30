//! Module re-exporting used types any polyfill to help with feature support.

#[cfg(feature = "std")]
mod std_imports {
    pub use std::rc::Rc;
    pub use std::sync::Arc;
    pub use std::sync::Mutex;
    pub use std::sync::MutexGuard;

    pub use std::alloc as allocator;
}

#[cfg(feature = "std")]
pub use std_imports::*;

#[cfg(feature = "no_std")]
mod nostd_imports {
    pub use spin::Mutex;
    pub use spin::MutexGuard;

    pub use alloc::alloc as allocator;

    pub use ::alloc::vec::Vec;

    pub use ::alloc::rc::Rc;
    pub use ::alloc::sync::Arc;
}
#[cfg(feature = "no_std")]
pub use nostd_imports::*;

use crate::error::{LockingError, MutexKind};

/// Trait that adds a method which mimics std `Result::map_err` on a Lock in
/// order to unify no_std and std environments.
///
/// This is necessary as [spin::Mutex::lock] doesn't return a Result but a
/// [MutexGuard] directly.
pub(crate) trait LockTypesafe<T> {
    fn lock_named(&self, which: MutexKind) -> Result<MutexGuard<T>, crate::error::LockingError>;
    fn try_lock_named(&self, which: MutexKind)
        -> Result<MutexGuard<T>, crate::error::LockingError>;
}
#[cfg(feature = "std")]
impl<T> LockTypesafe<T> for Mutex<T> {
    fn lock_named(&self, which: MutexKind) -> Result<MutexGuard<T>, crate::error::LockingError> {
        match self.lock() {
            Ok(it) => Ok(it),
            Err(_) => Err(LockingError::Poisoned { which }),
        }
    }
    fn try_lock_named(
        &self,
        which: MutexKind,
    ) -> Result<MutexGuard<T>, crate::error::LockingError> {
        match self.try_lock() {
            Ok(it) => Ok(it),
            Err(std::sync::TryLockError::Poisoned(_)) => Err(LockingError::Poisoned { which }),
            Err(std::sync::TryLockError::WouldBlock) => Err(LockingError::WouldBlock),
        }
    }
}
#[cfg(feature = "no_std")]
impl<T> LockTypesafe<T> for Mutex<T> {
    fn lock_named(&self, _which: MutexKind) -> Result<MutexGuard<T>, LockingError> {
        Ok(self.lock())
    }
    fn try_lock_named(
        &self,
        _which: MutexKind,
    ) -> Result<MutexGuard<T>, crate::error::LockingError> {
        match self.try_lock() {
            Some(it) => Ok(it),
            None => Err(LockingError::WouldBlock),
        }
    }
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

/// Type requirements for values that can be stored.
#[cfg(any(feature = "ptr_metadata", feature = "leak_data"))]
pub trait StoreRequirements: 'static {}
#[cfg(any(feature = "ptr_metadata", feature = "leak_data"))]
impl<T: 'static> StoreRequirements for T {}

/// Type requirements for values that can be stored.
#[cfg(all(not(feature = "ptr_metadata"), not(feature = "leak_data")))]
pub trait StoreRequirements: Copy {}
#[cfg(all(not(feature = "ptr_metadata"), not(feature = "leak_data")))]
impl<T: Copy> StoreRequirements for T {}

#[cfg(feature = "ptr_metadata")]
pub use core::marker::Unsize;
#[cfg(feature = "ptr_metadata")]
pub use core::ptr::{DynMetadata, Pointee};

#[cfg(feature = "ptr_metadata")]
mod pointer {
    use super::*;
    use core::ptr::NonNull;

    pub(crate) const fn static_metadata<S, T: ?Sized>() -> <T as Pointee>::Metadata
    where
        S: Unsize<T>,
    {
        let (_, metadata) = (NonNull::<S>::dangling().as_ptr() as *const T).to_raw_parts();
        metadata
    }

    /// Allows dynamically dropping arbitrary types.
    ///
    /// This is a workaround for invoking [`Drop::drop`] as well as calling
    /// compiler generated drop glue dynamically.
    pub(crate) trait HandleDrop {
        fn do_drop(&mut self);
    }
    impl<T: ?Sized> HandleDrop for T {
        #[inline(never)]
        fn do_drop(&mut self) {
            unsafe { core::ptr::drop_in_place(self as *mut Self) }
        }
    }
}
#[cfg(feature = "ptr_metadata")]
pub(crate) use pointer::*;
