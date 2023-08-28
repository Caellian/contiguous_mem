#[cfg(feature = "no_std")]
use alloc::alloc::LayoutError;
#[cfg(feature = "std")]
use std::alloc::LayoutError;

/// Represents errors that can occur while using the [`ContiguousMemory`](crate::ContiguousMemory) container.
#[derive(Debug)]
pub enum ContiguousMemoryError {
    /// Tried to store data that does not fit into any of the remaining free memory regions.
    NoStorageLeft,
    /// Attempted to occupy a memory region that is already marked as taken.
    AlreadyUsed,
    /// Attempted to operate on a memory region that is not contained within the [`AllocationTracker`](crate::AllocationTracker).
    NotContained,
    /// Attempted to free memory that has already been deallocated.
    DoubleFree,
    /// The [`AllocationTracker`](crate::AllocationTracker) does not allow shrinking to the expected size.
    Unshrinkable {
        /// The minimum required size for shrinking the [`ContiguousMemory`](crate::ContiguousMemory) container.
        min_required: usize,
    },
    /// Indicates that a mutex containing the base memory offset or the [`AllocationTracker`](crate::AllocationTracker) was poisoned.
    Poisoned {
        /// Specifies which component was poisoned: the base memory offset or the [`AllocationTracker`](crate::AllocationTracker).
        which: PoisonedMutex,
    },
    /// Attempted to borrow the [`AllocationTracker`](crate::AllocationTracker) which is already in use.
    TrackerInUse,
    /// Indicates that the provided [`Layout`](std::alloc::Layout) is invalid.
    Layout {
        /// The underlying error that caused the [`Layout`](std::alloc::Layout) to be considered invalid.
        source: LayoutError,
    },
}

/// Represents possible poisoning sources for mutexes in [`ContiguousMemoryError::Poisoned`].
#[derive(Debug)]
pub enum PoisonedMutex {
    /// Mutex containing the base memory offset was poisoned.
    BaseAddress,
    /// [`AllocationTracker`](crate::AllocationTracker) mutex was poisoned.
    AllocationTracker,
}

#[cfg(feature = "std")]
impl std::fmt::Display for ContiguousMemoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
            ContiguousMemoryError::Poisoned { which } => match which {
                PoisonedMutex::BaseAddress => {
                    write!(f, "Cannot acquire lock: base address Mutex was poisoned")
                }
                PoisonedMutex::AllocationTracker => write!(
                    f,
                    "Cannot acquire lock: AllocationTracker Mutex was poisoned"
                ),
            },
            ContiguousMemoryError::TrackerInUse => {
                write!(f, "Cannot borrow AllocationTracker: it is already in use")
            }
            ContiguousMemoryError::Layout { source } => write!(f, "Layout error: {}", source),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ContiguousMemoryError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ContiguousMemoryError::Layout { source } => Some(source),
            _ => None,
        }
    }
}

impl From<LayoutError> for ContiguousMemoryError {
    fn from(layout_err: LayoutError) -> Self {
        ContiguousMemoryError::Layout { source: layout_err }
    }
}
