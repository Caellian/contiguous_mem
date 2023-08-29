//! Module re-exporting used types to help with `no_std` support.

#[cfg(feature = "std")]
mod std_imports {
    pub use std::rc::Rc;
    pub use std::sync::Arc;
    pub use std::sync::Mutex;
    pub use std::sync::MutexGuard;

    pub use std::alloc;
}
#[cfg(feature = "std")]
pub use std_imports::*;

#[cfg(feature = "no_std")]
mod nostd_imports {
    pub use spin::Mutex;
    pub use spin::MutexGuard;

    pub use alloc::alloc;

    pub use ::alloc::vec::Vec;

    pub use ::alloc::rc::Rc;
    pub use ::alloc::sync::Arc;
}
#[cfg(feature = "no_std")]
pub use nostd_imports::*;

use crate::error::{LockingError, MutexKind};

/// Trait that adds a method which mimics std `Result::map_err` on a Lock in order to unify
/// no_std and std environments.
///
/// This is necessary as [spin::Mutex::lock] doesn't return a Result but a [MutexGuard]
/// directly.
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
        which: MutexKind,
    ) -> Result<MutexGuard<T>, crate::error::LockingError> {
        match self.try_lock() {
            Some(it) => Ok(it),
            None => Err(LockingError::WouldBlock),
        }
    }
}
