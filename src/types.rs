//! Module re-exporting used types and polyfill to help with feature support.

#[cfg(not(feature = "no_std"))]
mod std_imports {
    pub use std::rc::Rc;
    #[cfg(feature = "sync_impl")]
    pub use std::sync::{Arc, Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard};
}

#[cfg(not(feature = "no_std"))]
pub use std_imports::*;

#[cfg(feature = "no_std")]
mod nostd_imports {
    pub use ::alloc::rc::Rc;
    #[cfg(feature = "sync_impl")]
    pub use ::alloc::sync::Arc;
    #[cfg(feature = "sync_impl")]
    pub use spin::{Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard};

    pub use ::alloc::vec;
    pub use ::alloc::vec::Vec;
}
#[cfg(feature = "no_std")]
pub use nostd_imports::*;

#[cfg(feature = "sync_impl")]
use crate::error::{LockTarget, LockingError};

/// Trait that adds a method which mimics std `Result::map_err` on a Lock in
/// order to unify no_std and std environments.
///
/// This is necessary as [spin::Mutex::lock] doesn't return a Result but a
/// [MutexGuard] directly.
#[cfg(feature = "sync_impl")]
pub(crate) trait MutexTypesafe<T: ?Sized> {
    fn lock_named(&self, target: LockTarget) -> Result<MutexGuard<T>, crate::error::LockingError>;
    fn try_lock_named(
        &self,
        target: LockTarget,
    ) -> Result<MutexGuard<T>, crate::error::LockingError>;
}
#[cfg(all(feature = "sync_impl", not(feature = "no_std")))]
impl<T: ?Sized> MutexTypesafe<T> for Mutex<T> {
    fn lock_named(&self, target: LockTarget) -> Result<MutexGuard<T>, crate::error::LockingError> {
        match self.lock() {
            Ok(it) => Ok(it),
            Err(_) => Err(LockingError::Poisoned { target }),
        }
    }
    fn try_lock_named(
        &self,
        target: LockTarget,
    ) -> Result<MutexGuard<T>, crate::error::LockingError> {
        match self.try_lock() {
            Ok(it) => Ok(it),
            Err(std::sync::TryLockError::Poisoned(_)) => Err(LockingError::Poisoned { target }),
            Err(std::sync::TryLockError::WouldBlock) => Err(LockingError::WouldBlock { target }),
        }
    }
}
#[cfg(all(feature = "sync_impl", feature = "no_std"))]
impl<T: ?Sized> MutexTypesafe<T> for Mutex<T> {
    fn lock_named(&self, _target: LockTarget) -> Result<MutexGuard<T>, LockingError> {
        Ok(self.lock())
    }
    fn try_lock_named(
        &self,
        target: LockTarget,
    ) -> Result<MutexGuard<T>, crate::error::LockingError> {
        match self.try_lock() {
            Some(it) => Ok(it),
            None => Err(LockingError::WouldBlock { target }),
        }
    }
}

#[cfg(feature = "sync_impl")]
pub(crate) trait RwLockTypesafe<T: ?Sized> {
    fn read_named(&self, target: LockTarget) -> Result<RwLockReadGuard<T>, LockingError>;
    fn try_read_named(&self, target: LockTarget) -> Result<RwLockReadGuard<T>, LockingError>;
    fn write_named(&self, target: LockTarget) -> Result<RwLockWriteGuard<T>, LockingError>;
    fn try_write_named(&self, target: LockTarget) -> Result<RwLockWriteGuard<T>, LockingError>;
}
#[cfg(all(feature = "sync_impl", not(feature = "no_std")))]
impl<T: ?Sized> RwLockTypesafe<T> for RwLock<T> {
    fn read_named(&self, target: LockTarget) -> Result<RwLockReadGuard<T>, LockingError> {
        match self.read() {
            Ok(guard) => Ok(guard),
            Err(_) => Err(LockingError::Poisoned { target }),
        }
    }

    fn try_read_named(&self, target: LockTarget) -> Result<RwLockReadGuard<T>, LockingError> {
        match self.try_read() {
            Ok(guard) => Ok(guard),
            Err(std::sync::TryLockError::WouldBlock) => Err(LockingError::WouldBlock { target }),
            Err(std::sync::TryLockError::Poisoned(_)) => Err(LockingError::Poisoned { target }),
        }
    }

    fn write_named(&self, target: LockTarget) -> Result<RwLockWriteGuard<T>, LockingError> {
        match self.write() {
            Ok(guard) => Ok(guard),
            Err(_) => Err(LockingError::Poisoned { target }),
        }
    }

    fn try_write_named(&self, target: LockTarget) -> Result<RwLockWriteGuard<T>, LockingError> {
        match self.try_write() {
            Ok(guard) => Ok(guard),
            Err(std::sync::TryLockError::WouldBlock) => Err(LockingError::WouldBlock { target }),
            Err(std::sync::TryLockError::Poisoned(_)) => Err(LockingError::Poisoned { target }),
        }
    }
}
#[cfg(all(feature = "sync_impl", feature = "no_std"))]
impl<T: ?Sized> RwLockTypesafe<T> for RwLock<T> {
    fn read_named(&self, _target: LockTarget) -> Result<RwLockReadGuard<T>, LockingError> {
        Ok(self.read())
    }

    fn try_read_named(&self, target: LockTarget) -> Result<RwLockReadGuard<T>, LockingError> {
        match self.try_read() {
            Some(guard) => Ok(guard),
            None => Err(LockingError::WouldBlock { target }),
        }
    }

    fn write_named(&self, _target: LockTarget) -> Result<RwLockWriteGuard<T>, LockingError> {
        Ok(self.write())
    }

    fn try_write_named(&self, target: LockTarget) -> Result<RwLockWriteGuard<T>, LockingError> {
        match self.try_write() {
            Some(guard) => Ok(guard),
            None => Err(LockingError::WouldBlock { target }),
        }
    }
}
