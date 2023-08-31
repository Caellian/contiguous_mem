//! Module re-exporting used types any polyfill to help with feature support.

#[cfg(feature = "std")]
mod std_imports {
    pub use std::rc::Rc;
    pub use std::sync::Arc;
    pub use std::sync::Mutex;
    pub use std::sync::MutexGuard;
    pub use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard};

    pub use std::alloc as allocator;
}

#[cfg(feature = "std")]
pub use std_imports::*;

#[cfg(not(feature = "std"))]
mod nostd_imports {
    pub use spin::Mutex;
    pub use spin::MutexGuard;
    pub use spin::{RwLock, RwLockReadGuard, RwLockWriteGuard};

    pub use alloc::alloc as allocator;

    pub use ::alloc::vec::Vec;

    pub use ::alloc::rc::Rc;
    pub use ::alloc::sync::Arc;
}
#[cfg(not(feature = "std"))]
pub use nostd_imports::*;

use crate::error::{LockSource, LockingError};

/// Trait that adds a method which mimics std `Result::map_err` on a Lock in
/// order to unify no_std and std environments.
///
/// This is necessary as [spin::Mutex::lock] doesn't return a Result but a
/// [MutexGuard] directly.
pub(crate) trait MutexTypesafe<T: ?Sized> {
    fn lock_named(&self, source: LockSource) -> Result<MutexGuard<T>, crate::error::LockingError>;
    fn try_lock_named(
        &self,
        source: LockSource,
    ) -> Result<MutexGuard<T>, crate::error::LockingError>;
}
#[cfg(feature = "std")]
impl<T: ?Sized> MutexTypesafe<T> for Mutex<T> {
    fn lock_named(&self, source: LockSource) -> Result<MutexGuard<T>, crate::error::LockingError> {
        match self.lock() {
            Ok(it) => Ok(it),
            Err(_) => Err(LockingError::Poisoned { source }),
        }
    }
    fn try_lock_named(
        &self,
        source: LockSource,
    ) -> Result<MutexGuard<T>, crate::error::LockingError> {
        match self.try_lock() {
            Ok(it) => Ok(it),
            Err(std::sync::TryLockError::Poisoned(_)) => Err(LockingError::Poisoned { source }),
            Err(std::sync::TryLockError::WouldBlock) => Err(LockingError::WouldBlock),
        }
    }
}
#[cfg(not(feature = "std"))]
impl<T: ?Sized> MutexTypesafe<T> for Mutex<T> {
    fn lock_named(&self, _source: LockSource) -> Result<MutexGuard<T>, LockingError> {
        Ok(self.lock())
    }
    fn try_lock_named(
        &self,
        _source: LockSource,
    ) -> Result<MutexGuard<T>, crate::error::LockingError> {
        match self.try_lock() {
            Some(it) => Ok(it),
            None => Err(LockingError::WouldBlock),
        }
    }
}

pub(crate) trait RwLockTypesafe<T: ?Sized> {
    fn read_named(&self, source: LockSource) -> Result<RwLockReadGuard<T>, LockingError>;
    fn try_read_named(&self, source: LockSource) -> Result<RwLockReadGuard<T>, LockingError>;
    fn write_named(&self, source: LockSource) -> Result<RwLockWriteGuard<T>, LockingError>;
    fn try_write_named(&self, source: LockSource) -> Result<RwLockWriteGuard<T>, LockingError>;
}
#[cfg(feature = "std")]
impl<T: ?Sized> RwLockTypesafe<T> for RwLock<T> {
    fn read_named(&self, source: LockSource) -> Result<RwLockReadGuard<T>, LockingError> {
        match self.read() {
            Ok(guard) => Ok(guard),
            Err(_) => Err(LockingError::Poisoned { source }),
        }
    }

    fn try_read_named(&self, source: LockSource) -> Result<RwLockReadGuard<T>, LockingError> {
        match self.try_read() {
            Ok(guard) => Ok(guard),
            Err(std::sync::TryLockError::WouldBlock) => Err(LockingError::WouldBlock),
            Err(std::sync::TryLockError::Poisoned(_)) => Err(LockingError::Poisoned { source }),
        }
    }

    fn write_named(&self, source: LockSource) -> Result<RwLockWriteGuard<T>, LockingError> {
        match self.write() {
            Ok(guard) => Ok(guard),
            Err(_) => Err(LockingError::Poisoned { source }),
        }
    }

    fn try_write_named(&self, source: LockSource) -> Result<RwLockWriteGuard<T>, LockingError> {
        match self.try_write() {
            Ok(guard) => Ok(guard),
            Err(std::sync::TryLockError::WouldBlock) => Err(LockingError::WouldBlock),
            Err(std::sync::TryLockError::Poisoned(_)) => Err(LockingError::Poisoned { source }),
        }
    }
}
#[cfg(not(feature = "std"))]
impl<T: ?Sized> RwLockTypesafe<T> for RwLock<T> {
    fn read_named(&self, _source: LockSource) -> Result<RwLockReadGuard<T>, LockingError> {
        Ok(self.read())
    }

    fn try_read_named(&self, _source: LockSource) -> Result<RwLockReadGuard<T>, LockingError> {
        match self.try_read() {
            Some(guard) => Ok(guard),
            None => Err(LockingError::WouldBlock),
        }
    }

    fn write_named(&self, _source: LockSource) -> Result<RwLockWriteGuard<T>, LockingError> {
        Ok(self.write())
    }

    fn try_write_named(&self, _source: LockSource) -> Result<RwLockWriteGuard<T>, LockingError> {
        match self.try_write() {
            Some(guard) => Ok(guard),
            None => Err(LockingError::WouldBlock),
        }
    }
}

#[cfg(not(feature = "debug"))]
pub trait DebugReq {}
#[cfg(not(feature = "debug"))]
impl<T: ?Sized> DebugReq for T {}

#[cfg(feature = "debug")]
pub trait DebugReq: core::fmt::Debug {}
#[cfg(feature = "debug")]
impl<T: ?Sized + core::fmt::Debug> DebugReq for T {}

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
pub trait StoreRequirements: Copy + 'static {}
#[cfg(all(not(feature = "ptr_metadata"), not(feature = "leak_data")))]
impl<T: Copy + 'static> StoreRequirements for T {}

#[cfg(feature = "ptr_metadata")]
pub use core::marker::Unsize;
#[cfg(feature = "ptr_metadata")]
pub use core::ptr::{DynMetadata, Pointee};

#[cfg(feature = "ptr_metadata")]
mod pointer {
    use super::*;
    use core::ptr::NonNull;

    pub const fn static_metadata<S, T: ?Sized>() -> <T as Pointee>::Metadata
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
    pub trait HandleDrop {
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
