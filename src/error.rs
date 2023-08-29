//! Errors produced by the crate.

#[cfg(all(feature = "error_in_core", not(feature = "std")))]
use core::error::Error;
#[cfg(all(not(feature = "error_in_core"), feature = "std"))]
use std::error::Error;

#[cfg(feature = "std")]
use std::sync::MutexGuard;
#[cfg(feature = "std")]
use std::sync::PoisonError;

use core::alloc::LayoutError;
use core::fmt::{Debug, Display, Formatter, Result as FmtResult};

use crate::range::ByteRange;

/// Error returned when [`Mutex`](crate::types::Mutex) isn't lockable.
#[derive(Debug)]
pub enum LockingError {
    /// Not lockable because Mutex was poisoned.
    Poisoned {
        /// Specifies which component was poisoned.
        which: MutexKind,
    },
    /// Not lockable because the lock would be blocking.
    WouldBlock,
}

impl Display for LockingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            LockingError::Poisoned { which } => match which {
                MutexKind::BaseAddress => {
                    write!(f, "Cannot acquire lock: base address Mutex was poisoned")
                }
                MutexKind::AllocationTracker => write!(
                    f,
                    "Cannot acquire lock: AllocationTracker Mutex was poisoned"
                ),
                MutexKind::Reference => write!(
                    f,
                    "Cannot acquire lock: reference concurrent mutable access exclusion flag Mutex was poisoned"
                )
            },
            LockingError::WouldBlock => write!(f, "Lock would be block"),
        }
    }
}

#[cfg(any(feature = "std", feature = "error_in_core"))]
impl Error for LockingError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

#[cfg(feature = "std")]
impl From<PoisonError<MutexGuard<'_, *mut u8>>> for LockingError {
    fn from(_: PoisonError<MutexGuard<'_, *mut u8>>) -> Self {
        LockingError::Poisoned {
            which: MutexKind::BaseAddress,
        }
    }
}

#[cfg(feature = "std")]
impl From<PoisonError<MutexGuard<'_, crate::tracker::AllocationTracker>>> for LockingError {
    fn from(_: PoisonError<MutexGuard<'_, crate::tracker::AllocationTracker>>) -> Self {
        LockingError::Poisoned {
            which: MutexKind::AllocationTracker,
        }
    }
}

#[cfg(feature = "std")]
impl<T> From<std::sync::TryLockError<T>> for LockingError
where
    LockingError: From<PoisonError<T>>,
{
    fn from(value: std::sync::TryLockError<T>) -> Self {
        match value {
            std::sync::TryLockError::Poisoned(poison_err) => LockingError::from(poison_err),
            std::sync::TryLockError::WouldBlock => LockingError::WouldBlock,
        }
    }
}

/// Error returned when multiple concurrent mutable access' are attempted to
/// the same memory region.
#[derive(Debug)]
pub struct BorrowMutError {
    /// [`ByteRange`] that was attempted to be borrowed.
    pub range: ByteRange,
}

impl Display for BorrowMutError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "attempted to mutably borrow already borrowed memory region: {}",
            self.range
        )
    }
}

#[cfg(any(feature = "std", feature = "error_in_core"))]
impl Error for BorrowMutError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

/// Represents errors that can occur while using the
/// [`ContiguousMemory`](crate::ContiguousMemory) container.
#[derive(Debug)]
pub enum ContiguousMemoryError {
    /// Tried to store data that does not fit into any of the remaining free
    /// memory regions.
    NoStorageLeft,
    /// Attempted to occupy a memory region that is already marked as taken.
    AlreadyUsed,
    /// Attempted to operate on a memory region that is not contained within the
    /// [`AllocationTracker`](crate::AllocationTracker).
    NotContained,
    /// Attempted to free memory that has already been deallocated.
    DoubleFree,
    /// The [`AllocationTracker`](crate::AllocationTracker) does not allow
    /// shrinking to the expected size.
    Unshrinkable {
        /// The minimum required size for shrinking the
        /// [`ContiguousMemory`](crate::ContiguousMemory) container.
        min_required: usize,
    },
    /// Indicates that a mutex wasn't lockable.
    Lock(LockingError),
    /// Attempted to borrow the [`AllocationTracker`](crate::AllocationTracker)
    /// which is already in use.
    TrackerInUse,
    /// Indicates that the provided [`Layout`](std::alloc::Layout) is invalid.
    Layout(
        /// The underlying error that caused the [`Layout`](std::alloc::Layout)
        /// to be considered invalid.
        LayoutError,
    ),
    /// Tried mutably borrowing already borrowed region of memory
    BorrowMut(BorrowMutError),
}

/// Represents possible poisoning sources for mutexes in [`LockingError`].
#[derive(Debug, Clone, Copy)]
pub enum MutexKind {
    /// Mutex containing the base memory offset was poisoned.
    BaseAddress,
    /// [`AllocationTracker`](crate::AllocationTracker) mutex was poisoned.
    AllocationTracker,
    /// Concurrent mutable access exclusion flag mutex in
    /// [`ReferenceState`](crate::ReferenceState) was poisoned.
    Reference,
}

#[cfg(feature = "std")]
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
            ContiguousMemoryError::Unshrinkable { min_required } => write!(
                f,
                "Cannot shrink memory regions; minimum required space: {} bytes",
                min_required
            ),
            ContiguousMemoryError::Lock(it) => write!(f, "Poison error: {}", it),
            ContiguousMemoryError::TrackerInUse => {
                write!(f, "Cannot borrow AllocationTracker: it is already in use")
            }
            ContiguousMemoryError::Layout(it) => write!(f, "Layout error: {}", it),
            ContiguousMemoryError::BorrowMut(it) => write!(f, "Borrow mutable error: {}", it),
        }
    }
}

#[cfg(any(feature = "std", feature = "error_in_core"))]
impl Error for ContiguousMemoryError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ContiguousMemoryError::Layout(it) => Some(it),
            ContiguousMemoryError::Lock(it) => Some(it),
            _ => None,
        }
    }
}

impl From<LockingError> for ContiguousMemoryError {
    fn from(layout_err: LockingError) -> Self {
        ContiguousMemoryError::Lock(layout_err)
    }
}

impl From<LayoutError> for ContiguousMemoryError {
    fn from(layout_err: LayoutError) -> Self {
        ContiguousMemoryError::Layout(layout_err)
    }
}
