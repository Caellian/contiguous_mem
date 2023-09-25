//! Errors produced by the crate.

#[cfg(feature = "error_in_core")]
use core::error::Error;
#[cfg(all(not(feature = "error_in_core"), not(feature = "no_std")))]
use std::error::Error;

#[cfg(not(feature = "no_std"))]
use std::sync::MutexGuard;
#[cfg(not(feature = "no_std"))]
use std::sync::PoisonError;

use core::alloc::LayoutError;
use core::fmt::Debug;
#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
use core::fmt::{Display, Formatter, Result as FmtResult};

use crate::range::ByteRange;

/// Represents a class of errors returned by invalid memory operations and
/// allocator failiure.
#[derive(Debug)]
pub enum MemoryError {
    /// Invalid memory layout.
    Layout(LayoutError),
    /// Allocation failure caused by either resource exhaustion or invalid
    /// arguments being provided to an allocator.
    Allocator(
        #[cfg(feature = "allocator_api")] core::alloc::AllocError,
        #[cfg(not(feature = "allocator_api"))] (),
    ),
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Display for MemoryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "Memory manager error")
    }
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Error for MemoryError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            MemoryError::Layout(inner) => Some(inner),
            #[cfg(feature = "allocator_api")]
            MemoryError::Allocator(inner) => Some(inner),
            #[cfg(not(feature = "allocator_api"))]
            MemoryError::Allocator(()) => None,
        }
    }
}

impl From<LayoutError> for MemoryError {
    fn from(err: LayoutError) -> Self {
        MemoryError::Layout(err)
    }
}

#[cfg(feature = "allocator_api")]
impl From<core::alloc::AllocError> for MemoryError {
    fn from(err: core::alloc::AllocError) -> Self {
        MemoryError::Allocator(err)
    }
}

/// Error indicating that the container is full.
#[derive(Debug)]
pub struct NoFreeMemoryError;

/// Represents possible poisoning sources for mutexes and locks.
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
#[cfg(feature = "sync_impl")]
pub enum LockTarget {
    /// Mutex containing the base memory offset was poisoned.
    BaseAddress,
    /// Allocation tracker mutex was poisoned.
    AllocationTracker,
    /// Concurrent mutable access exclusion flag in reference state was poisoned.
    Reference,
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Display for NoFreeMemoryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "Insufficient free memory")
    }
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Error for NoFreeMemoryError {}

/// Error returned when concurrent mutable access is attempted to the same
/// memory region.
#[derive(Debug)]
pub struct RegionBorrowError {
    /// [`ByteRange`] that was attempted to be borrowed.
    pub range: ByteRange,
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Display for RegionBorrowError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "attempted to borrow already mutably borrowed memory region: {}",
            self.range
        )
    }
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Error for RegionBorrowError {}

/// Error returned when a [`Mutex`](crate::types::Mutex) or a
/// [`RwLock`](crate::types::RwLock) isn't lockable.
#[derive(Debug)]
#[cfg(feature = "sync_impl")]
pub enum LockingError {
    /// Not lockable because the mutex/lock was poisoned.
    Poisoned {
        /// Specifies source of poisoning.
        target: LockTarget,
    },
    /// Not lockable because the lock would be blocking.
    WouldBlock {
        /// Specifies which mutex/lock would block.
        target: LockTarget,
    },
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
#[cfg(feature = "sync_impl")]
impl Display for LockingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            LockingError::Poisoned { target } => write!(
                f,
                "Cannot acquire lock: {}",
                match target {
                    LockTarget::BaseAddress => {
                        "base address Mutex was poisoned"
                    }
                    LockTarget::AllocationTracker => "AllocationTracker Mutex was poisoned",
                    LockTarget::Reference =>
                        "reference concurrent mutable access exclusion flag Mutex was poisoned",
                }
            ),
            LockingError::WouldBlock { target } => write!(
                f,
                "Lock would block the current thread: {}",
                match target {
                    LockTarget::BaseAddress => "base address already borrowed",
                    LockTarget::AllocationTracker => "AllocationTracker already borrowed",
                    LockTarget::Reference => "reference already borrowed",
                }
            ),
        }
    }
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
#[cfg(feature = "sync_impl")]
impl Error for LockingError {}

#[cfg(not(feature = "no_std"))]
#[cfg(feature = "sync_impl")]
impl From<PoisonError<MutexGuard<'_, *mut u8>>> for LockingError {
    fn from(_: PoisonError<MutexGuard<'_, *mut u8>>) -> Self {
        LockingError::Poisoned {
            target: LockTarget::BaseAddress,
        }
    }
}

#[cfg(not(feature = "no_std"))]
#[cfg(feature = "sync_impl")]
impl From<PoisonError<MutexGuard<'_, crate::tracker::AllocationTracker>>> for LockingError {
    fn from(_: PoisonError<MutexGuard<'_, crate::tracker::AllocationTracker>>) -> Self {
        LockingError::Poisoned {
            target: LockTarget::AllocationTracker,
        }
    }
}

#[cfg(feature = "sync_impl")]
/// A wrapper that represents either a memory error or a locking error.
pub enum SyncMemoryError {
    /// A memory error.
    Memory(MemoryError),
    /// A locking error.
    Lock(LockingError),
}

impl From<MemoryError> for SyncMemoryError {
    fn from(err: MemoryError) -> Self {
        SyncMemoryError::Memory(err)
    }
}
impl From<LockingError> for SyncMemoryError {
    fn from(err: LockingError) -> Self {
        SyncMemoryError::Lock(err)
    }
}
