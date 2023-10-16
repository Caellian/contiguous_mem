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

#[cfg(feature = "error_in_core")]
pub use core::error::Error;
use core::{
    cell::UnsafeCell,
    convert::Infallible,
};
#[cfg(all(not(feature = "error_in_core"), not(feature = "no_std")))]
pub use std::error::Error;

use crate::error::LockTarget;
#[cfg(feature = "sync_impl")]
use crate::error::LockingError;

/// Unifies reading behavior from structs that provide inner mutability.
/// 
/// All implemented functions should be `#[inline]`d to ensure that final code
/// behaves as if this abstraction didn't exist.
/// 
/// This allows different [`ContigousMemory`](crate::ContigousMemory)
/// implementation details to use the same code base while staying correct for
/// the strictest (`ImplConcurrent`) one.
pub(crate) trait ReadableInner<T: ?Sized> {
    type ReadGuard<'a>: core::ops::Deref<Target = T>
    where
        Self: 'a;
    #[cfg(not(any(feature = "error_in_core", not(feature = "no_std"))))]
    type BorrowError;
    #[cfg(any(feature = "error_in_core", not(feature = "no_std")))]
    type BorrowError: Error;

    fn read_named(&self, target: LockTarget) -> Result<Self::ReadGuard<'_>, Self::BorrowError>;
    fn try_read_named(&self, target: LockTarget) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        self.read_named(target)
    }
}

/// Unifies writing behavior from structs that provide inner mutability.
/// 
/// See [`ReadableInner`] for more details.
pub(crate) trait WritableInner<T: ?Sized>: ReadableInner<T> {
    type WriteGuard<'a>: core::ops::DerefMut<Target = T>
    where
        Self: 'a;
    #[cfg(not(any(feature = "error_in_core", not(feature = "no_std"))))]
    type MutBorrowError;
    #[cfg(any(feature = "error_in_core", not(feature = "no_std")))]
    type MutBorrowError: Error;

    fn write_named(&self, target: LockTarget)
        -> Result<Self::WriteGuard<'_>, Self::MutBorrowError>;
    fn try_write_named(
        &self,
        target: LockTarget,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        self.write_named(target)
    }
}
#[cfg(all(feature = "sync_impl", not(feature = "no_std")))]
impl<T: ?Sized> ReadableInner<T> for Mutex<T> {
    type ReadGuard<'a> = MutexGuard<'a, T>
    where
        Self: 'a;
    type BorrowError = LockingError;
    #[inline]
    fn read_named(&self, target: LockTarget) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        match self.lock() {
            Ok(it) => Ok(it),
            Err(_) => Err(LockingError::Poisoned { target }),
        }
    }
    #[inline]
    fn try_read_named(&self, target: LockTarget) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        match self.try_lock() {
            Ok(it) => Ok(it),
            Err(std::sync::TryLockError::Poisoned(_)) => Err(LockingError::Poisoned { target }),
            Err(std::sync::TryLockError::WouldBlock) => Err(LockingError::WouldBlock { target }),
        }
    }
}
#[cfg(all(feature = "sync_impl", not(feature = "no_std")))]
impl<T: ?Sized> WritableInner<T> for Mutex<T> {
    type WriteGuard<'a> = MutexGuard<'a, T>
    where
        Self: 'a;
    type MutBorrowError = LockingError;

    #[inline]
    fn write_named(
        &self,
        target: LockTarget,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        match self.lock() {
            Ok(it) => Ok(it),
            Err(_) => Err(LockingError::Poisoned { target }),
        }
    }
    #[inline]
    fn try_write_named(
        &self,
        target: LockTarget,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        match self.try_lock() {
            Ok(it) => Ok(it),
            Err(std::sync::TryLockError::Poisoned(_)) => Err(LockingError::Poisoned { target }),
            Err(std::sync::TryLockError::WouldBlock) => Err(LockingError::WouldBlock { target }),
        }
    }
}
#[cfg(all(feature = "sync_impl", feature = "no_std"))]
impl<T: ?Sized> ReadableInner<T> for Mutex<T> {
    type ReadGuard<'a> = MutexGuard<'a, T>
    where
        Self: 'a;
    type BorrowError = LockingError;
    #[inline]
    fn read_named(&self, _target: LockTarget) -> Result<Self::ReadGuard, Self::BorrowError> {
        Ok(self.lock())
    }
    #[inline]
    fn try_read_named(&self, target: LockTarget) -> Result<Self::ReadGuard, Self::BorrowError> {
        match self.try_lock() {
            Some(it) => Ok(it),
            None => Err(LockingError::WouldBlock { target }),
        }
    }
}
#[cfg(all(feature = "sync_impl", feature = "no_std"))]
impl<T: ?Sized> WritableInner<T> for Mutex<T> {
    type WriteGuard<'a> = MutexGuard<'a, T>
    where
        Self: 'a;
    type MutBorrowError = LockingError;

    #[inline]
    fn write_named(
        &self,
        _target: LockTarget,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        Ok(self.lock())
    }
    #[inline]
    fn try_write_named(
        &self,
        target: LockTarget,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        match self.try_lock() {
            Some(it) => Ok(it),
            None => Err(LockingError::WouldBlock { target }),
        }
    }
}

#[cfg(all(feature = "sync_impl", not(feature = "no_std")))]
impl<T: ?Sized> ReadableInner<T> for RwLock<T> {
    type ReadGuard<'a> = RwLockReadGuard<'a, T>
    where
        Self: 'a;
    type BorrowError = LockingError;
    #[inline]
    fn read_named(&self, target: LockTarget) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        match self.read() {
            Ok(guard) => Ok(guard),
            Err(_) => Err(LockingError::Poisoned { target }),
        }
    }
    #[inline]
    fn try_read_named(&self, target: LockTarget) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        match self.try_read() {
            Ok(guard) => Ok(guard),
            Err(std::sync::TryLockError::WouldBlock) => Err(LockingError::WouldBlock { target }),
            Err(std::sync::TryLockError::Poisoned(_)) => Err(LockingError::Poisoned { target }),
        }
    }
}
#[cfg(all(feature = "sync_impl", not(feature = "no_std")))]
impl<T: ?Sized> WritableInner<T> for RwLock<T> {
    type WriteGuard<'a> = RwLockWriteGuard<'a, T>
    where
        Self: 'a;
    type MutBorrowError = LockingError;

    #[inline]
    fn write_named(
        &self,
        target: LockTarget,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        match self.write() {
            Ok(guard) => Ok(guard),
            Err(_) => Err(LockingError::Poisoned { target }),
        }
    }
    #[inline]
    fn try_write_named(
        &self,
        target: LockTarget,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        match self.try_write() {
            Ok(guard) => Ok(guard),
            Err(std::sync::TryLockError::WouldBlock) => Err(LockingError::WouldBlock { target }),
            Err(std::sync::TryLockError::Poisoned(_)) => Err(LockingError::Poisoned { target }),
        }
    }
}
#[cfg(all(feature = "sync_impl", feature = "no_std"))]
impl<T: ?Sized> ReadableInner<T> for RwLock<T> {
    type ReadGuard<'a> = RwLockReadGuard<'a, T>
    where
        Self: 'a;
    type BorrowError = LockingError;

    #[inline]
    fn read_named(&self, _target: LockTarget) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        Ok(self.read())
    }
    #[inline]
    fn try_read_named(&self, target: LockTarget) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        match self.try_read() {
            Some(guard) => Ok(guard),
            None => Err(LockingError::WouldBlock { target }),
        }
    }
}
#[cfg(all(feature = "sync_impl", feature = "no_std"))]
impl<T: ?Sized> WritableInner<T> for RwLock<T> {
    type WriteGuard<'a> = RwLockWriteGuard<'a, T>
    where
        Self: 'a;
    type MutBorrowError = LockingError;

    #[inline]
    fn write_named(
        &self,
        _target: LockTarget,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        Ok(self.write())
    }
    #[inline]
    fn try_write_named(
        &self,
        target: LockTarget,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        match self.try_write() {
            Some(guard) => Ok(guard),
            None => Err(LockingError::WouldBlock { target }),
        }
    }
}
impl<T: Copy> ReadableInner<T> for core::cell::Cell<T> {
    type ReadGuard<'a> = Owned<T> 
    where
        Self: 'a;
    type BorrowError = Infallible;

    #[inline]
    fn read_named(&self, _target: LockTarget) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        Ok(Owned(self.get()))
    }
    #[inline]
    fn try_read_named(&self, _target: LockTarget) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        Ok(Owned(self.get()))
    }
}

impl<T: Copy> WritableInner<T> for core::cell::Cell<T> {
    type WriteGuard<'a> = CellWriteGuard<'a, T>
    where
        Self: 'a;
    type MutBorrowError = Infallible;

    #[inline]
    fn write_named(
        &self,
        _target: LockTarget,
    ) -> Result<Self::WriteGuard<'_>, Infallible> {
        Ok(CellWriteGuard { parent: &self, value: self.get() })
    }
}
impl<T: ?Sized> ReadableInner<T> for core::cell::RefCell<T> {
    type ReadGuard<'a> = core::cell::Ref<'a, T> 
    where
        Self: 'a;
    type BorrowError = core::cell::BorrowError;

    #[inline]
    fn read_named(&self, _target: LockTarget) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        Ok(self.borrow())
    }
}

impl<T: ?Sized> WritableInner<T> for core::cell::RefCell<T> {
    type WriteGuard<'a> = core::cell::RefMut<'a, T>
    where
        Self: 'a;
    type MutBorrowError = core::cell::BorrowMutError;

    #[inline]
    fn write_named(
        &self,
        _target: LockTarget,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        Ok(self.borrow_mut())
    }
    #[inline]
    fn try_write_named(
        &self,
        _target: LockTarget,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        self.try_borrow_mut()
    }
}
impl<T: ?Sized> ReadableInner<T> for UnsafeCell<T> {
    type ReadGuard<'a> = &'a T
    where
        Self: 'a;
    type BorrowError = Infallible;
    #[inline]
    fn read_named(&self, _target: LockTarget) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        unsafe { Ok(&*self.get()) }
    }
}
impl<T: ?Sized> WritableInner<T> for UnsafeCell<T> {
    type WriteGuard<'a> = &'a mut T
    where
        Self: 'a;
    type MutBorrowError = Infallible;

    #[inline]
    fn write_named(
        &self,
        _target: LockTarget,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        unsafe { Ok(&mut *self.get())}
    }
}

/// Allows use of owned types through interfaces that require a
/// [`Deref`](core::ops::Deref) bound.
/// 
/// This allows owned type to be passed through [`ReadableInner`] and
/// [`WritableInner`], as well as owned state in unsafe implementation to be
/// treated as a [`Reference`] even though it isn't one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg(feature = "unsafe_impl")]
pub(crate) struct Owned<T>(pub(crate) T);
#[cfg(feature = "unsafe_impl")]
impl<T> std::ops::Deref for Owned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
#[cfg(feature = "unsafe_impl")]
impl<T> std::ops::DerefMut for Owned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Unifies construction of smart pointers and [`Owned`] via an owned value.
pub(crate) trait Reference<T>: core::ops::Deref<Target = T> {
    fn new(value: T) -> Self;
}

impl<T> Reference<T> for Rc<T> {
    fn new(value: T) -> Self {
        Rc::new(value)
    }
}
#[cfg(feature = "sync_impl")]
impl<T> Reference<T> for Arc<T> {
    fn new(value: T) -> Self {
        Arc::new(value)
    }
}
#[cfg(feature = "unsafe_impl")]
impl<T> Reference<T> for Owned<T> {
    fn new(value: T) -> Self {
        Owned(value)
    }
}

/// Allows using [`Cell`](core::cell::Cell) through the same interface as
/// [`RefCell`](core::cell::RefCell) and sync code.
pub(crate) struct CellWriteGuard<'a, T: Copy + 'a> {
    parent: &'a core::cell::Cell<T>,
    value: T,
}

impl<'a, T: Copy + 'a> Drop for CellWriteGuard<'a, T> {
    #[inline]
    fn drop(&mut self) {
        self.parent.set(self.value);
    }
}

impl<'a, T: Copy + 'a> core::ops::Deref for CellWriteGuard<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<'a, T: Copy + 'a> core::ops::DerefMut for CellWriteGuard<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}
