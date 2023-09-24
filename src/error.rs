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

/// Error returned when a [`Mutex`](crate::types::Mutex) or a
/// [`RwLock`](crate::types::RwLock) isn't lockable.
#[derive(Debug)]
#[cfg(feature = "sync")]
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
#[cfg(feature = "sync")]
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
#[cfg(feature = "sync")]
impl Error for LockingError {}

#[cfg(not(feature = "no_std"))]
#[cfg(feature = "sync")]
impl From<PoisonError<MutexGuard<'_, *mut u8>>> for LockingError {
    fn from(_: PoisonError<MutexGuard<'_, *mut u8>>) -> Self {
        LockingError::Poisoned {
            target: LockTarget::BaseAddress,
        }
    }
}

#[cfg(not(feature = "no_std"))]
#[cfg(feature = "sync")]
impl From<PoisonError<MutexGuard<'_, crate::tracker::AllocationTracker>>> for LockingError {
    fn from(_: PoisonError<MutexGuard<'_, crate::tracker::AllocationTracker>>) -> Self {
        LockingError::Poisoned {
            target: LockTarget::AllocationTracker,
        }
    }
}

/// Error returned when concurrent mutable access is attempted to the same
/// memory region.
#[derive(Debug)]
pub struct RegionBorrowedError {
    /// [`ByteRange`] that was attempted to be borrowed.
    pub range: ByteRange,
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Display for RegionBorrowedError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "attempted to borrow already mutably borrowed memory region: {}",
            self.range
        )
    }
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Error for RegionBorrowedError {}

/// Unable to handle allocator operation.
///
/// This can happen either due to resource exhaustion or the allocator not
/// supporting a requested operation.
#[derive(Debug)]
pub struct MemoryManagerError;

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Display for MemoryManagerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "Memory manager error")
    }
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Error for MemoryManagerError {}

#[cfg(feature = "allocator_api")]
impl From<core::alloc::AllocError> for MemoryManagerError {
    fn from(_: core::alloc::AllocError) -> Self {
        MemoryManagerError
    }
}

/// Represents errors that can occur while using the
/// [`ContiguousMemory`](crate::ContiguousMemory) container.
#[derive(Debug)]
#[non_exhaustive]
pub enum ContiguousMemoryError {
    /// Tried to store data that does not fit into any of the remaining free
    /// memory regions.
    NoStorageLeft,
    /// Attempted to occupy a memory region that is already marked as taken.
    AlreadyUsed,
    /// Attempted to operate on a memory region that is not contained within the
    /// allocation tracker.
    NotContained,
    /// Attempted to free memory that has already been deallocated.
    DoubleFree,
    /// The allocation tracker does not allow shrinking to the expected size due
    /// to previously stored data.
    Unshrinkable {
        /// The minimum required size to house currently stored data.
        required_size: usize,
    },
    /// Indicates that a mutex wasn't lockable.
    #[cfg(feature = "sync")]
    Lock(LockingError),
    /// Indicates that the provided [`Layout`](core::alloc::Layout) is invalid.
    Layout(
        /// The underlying error returned by `Layout` constructor.
        LayoutError,
    ),
    /// Tried mutably borrowing already borrowed region of memory
    BorrowMut(RegionBorrowedError),
    /// A memory manager error.
    MemoryManager(MemoryManagerError),
}

/// Represents possible poisoning sources for mutexes and locks.
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
#[cfg(feature = "sync")]
pub enum LockTarget {
    /// Mutex containing the base memory offset was poisoned.
    BaseAddress,
    /// Allocation tracker mutex was poisoned.
    AllocationTracker,
    /// Concurrent mutable access exclusion flag in reference state was poisoned.
    Reference,
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Display for ContiguousMemoryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            ContiguousMemoryError::NoStorageLeft => {
                write!(f, "Insufficient free storage available")
            }
            ContiguousMemoryError::NotContained => {
                write!(f, "Attempted to mark a memory region that isn't contained")
            }
            ContiguousMemoryError::AlreadyUsed => write!(
                f,
                "Attempted to take a memory region that is already marked as occupied"
            ),
            ContiguousMemoryError::DoubleFree => write!(
                f,
                "Attempted to free a memory region that is already marked as free"
            ),
            ContiguousMemoryError::Unshrinkable {
                required_size: min_required,
            } => write!(
                f,
                "Cannot shrink memory regions; minimum required space: {} bytes",
                min_required
            ),
            #[cfg(feature = "sync")]
            ContiguousMemoryError::Lock(it) => write!(f, "Poison error: {}", it),
            ContiguousMemoryError::Layout(it) => write!(f, "Layout error: {}", it),
            ContiguousMemoryError::BorrowMut(it) => write!(f, "Borrow mutable error: {}", it),
            ContiguousMemoryError::MemoryManager(it) => Display::fmt(it, f),
        }
    }
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Error for ContiguousMemoryError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ContiguousMemoryError::Layout(it) => Some(it),
            #[cfg(feature = "sync")]
            ContiguousMemoryError::Lock(it) => Some(it),
            ContiguousMemoryError::MemoryManager(it) => Some(it),
            _ => None,
        }
    }
}

#[cfg(feature = "sync")]
impl From<LockingError> for ContiguousMemoryError {
    fn from(err: LockingError) -> Self {
        ContiguousMemoryError::Lock(err)
    }
}

impl From<LayoutError> for ContiguousMemoryError {
    fn from(err: LayoutError) -> Self {
        ContiguousMemoryError::Layout(err)
    }
}

impl From<MemoryManagerError> for ContiguousMemoryError {
    fn from(err: MemoryManagerError) -> Self {
        ContiguousMemoryError::MemoryManager(err)
    }
}

#[cfg(feature = "allocator_api")]
impl From<core::alloc::AllocError> for ContiguousMemoryError {
    fn from(_: core::alloc::AllocError) -> Self {
        ContiguousMemoryError::MemoryManager(MemoryManagerError)
    }
}
