//! Implementation details for behavior specialization marker structs.
//!
//! End-users aren't meant to interact with traits defined in this module
//! directly and they exist solely to simplify implementation of
//! [`ContiguousMemoryStorage`](ContiguousMemoryStorage) by erasing
//! type details of different implementations.
//!
//! Any changes to these traits aren't considered a breaking change and won't
//! be reflected in version numbers.

use core::{
    alloc::Layout,
    cell::{Cell, RefCell, RefMut},
};

use crate::{
    raw::{base_addr_layout, BaseAddress, ManageMemory},
    types::*,
};

use crate::{range::ByteRange, refs::sealed::*, tracker::AllocationTracker, MemoryState};

#[cfg(feature = "sync_impl")]
use crate::error::{LockTarget, LockingError};

/// Implementation details shared between [storage](StorageDetails) and
/// [`reference`](ReferenceDetails) implementations.
pub trait ImplDetails<A: ManageMemory>: Sized {
    /// The type representing the base memory and allocation tracking.
    type Base;
    /// The type representing the allocation tracker discrete type.
    type AllocationTracker;
    /// The type representing the allocation tracker reference type.
    type ATGuard<'a>;
    /// The type representing result of accessing data that is locked in async
    /// context
    type LockResult<T>;

    /// Retrieves the base pointer from the `base` instance.
    fn get_base(base: &Self::Base) -> Self::LockResult<BaseAddress>;

    /// Constructs a layout from `base` instance and `alig`n.
    fn get_layout(base: &Self::Base, align: usize) -> Layout;

    /// Deallocates the `base` memory using `layout` information.
    unsafe fn deallocate(alloc: &A, base: &mut Self::Base, layout: Layout);
}

/// Implementation that's not thread-safe but performs faster as it avoids
/// mutexes and locks.
///
/// For example usage of default implementation see: [`ContiguousMemory`](crate::ContiguousMemory)
#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ImplDefault;
impl<A: ManageMemory> ImplDetails<A> for ImplDefault {
    type Base = Cell<BaseAddress>;
    type AllocationTracker = RefCell<AllocationTracker>;
    type ATGuard<'a> = RefMut<'a, AllocationTracker>;
    type LockResult<T> = T;

    #[inline]
    fn get_base(base: &Self::Base) -> Self::LockResult<BaseAddress> {
        base.get()
    }

    #[inline]
    fn get_layout(base: &Self::Base, align: usize) -> Layout {
        unsafe { base_addr_layout(<Self as ImplDetails<A>>::get_base(base), align) }
    }

    #[inline]
    unsafe fn deallocate(alloc: &A, base: &mut Self::Base, layout: Layout) {
        unsafe { alloc.deallocate(base.get(), layout) };
        base.set(None)
    }
}

/// Thread-safe implementation utilizing mutexes and locks to prevent data
/// races.
///
/// For example usage of default implementation see:
/// [`SyncContiguousMemory`](crate::SyncContiguousMemory)
#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg(feature = "sync_impl")]
pub struct ImplConcurrent;
#[cfg(feature = "sync_impl")]
impl<A: ManageMemory> ImplDetails<A> for ImplConcurrent {
    type Base = RwLock<BaseAddress>;
    type AllocationTracker = Mutex<AllocationTracker>;
    type ATGuard<'a> = MutexGuard<'a, AllocationTracker>;
    type LockResult<T> = Result<T, LockingError>;

    #[inline]
    fn get_base(base: &Self::Base) -> Self::LockResult<BaseAddress> {
        base.read_named(LockTarget::BaseAddress)
            .map(|result| *result)
    }

    #[inline]
    fn get_layout(base: &Self::Base, align: usize) -> Layout {
        unsafe {
            base_addr_layout(
                <Self as ImplDetails<A>>::get_base(base).unwrap_or_else(|_| None),
                align,
            )
        }
    }

    #[inline]
    unsafe fn deallocate(alloc: &A, base: &mut Self::Base, layout: Layout) {
        if let Ok(mut lock) = base.write_named(LockTarget::BaseAddress) {
            unsafe { alloc.deallocate(*lock, layout) };
            *lock = None;
        }
    }
}

/// Implementation which provides direct (unsafe) access to stored entries.
///
/// For example usage of default implementation see:
/// [`UnsafeContiguousMemory`](crate::UnsafeContiguousMemory)
#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg(feature = "unsafe_impl")]
pub struct ImplUnsafe;
#[cfg(feature = "unsafe_impl")]
impl<A: ManageMemory> ImplDetails<A> for ImplUnsafe {
    type Base = BaseAddress;
    type AllocationTracker = AllocationTracker;
    type ATGuard<'a> = &'a mut AllocationTracker;
    type LockResult<T> = T;

    #[inline]
    fn get_base(base: &Self::Base) -> Self::LockResult<BaseAddress> {
        *base
    }

    #[inline]
    fn get_layout(base: &Self::Base, align: usize) -> Layout {
        unsafe { base_addr_layout(<Self as ImplDetails<A>>::get_base(base), align) }
    }

    #[inline]
    unsafe fn deallocate(alloc: &A, base: &mut Self::Base, layout: Layout) {
        unsafe {
            alloc.deallocate(*base, layout);
        }
        *base = None;
    }
}

pub trait ImplReferencing<A: ManageMemory>: ImplDetails<A> {
    /// The type representing internal state of the reference.
    type RefState<T: ?Sized>: Clone;

    /// The type handling concurrent mutable access exclusion.
    type BorrowLock;

    /// Type of the concurrent mutable access exclusion read guard.
    type ReadGuard<'a>: DebugReq;
    /// Type of the concurrent mutable access exclusion write guard.
    type WriteGuard<'a>: DebugReq;

    /// The type representing reference to internal state
    type StorageState: core::ops::Deref<Target = MemoryState<Self, A>>;

    /// Retrieves the base pointer from the base instance. Non blocking version.
    #[inline]
    fn try_get_base(base: &Self::Base) -> Self::LockResult<BaseAddress> {
        Self::get_base(base)
    }

    /// Returns a writable reference to AllocationTracker.
    fn get_allocation_tracker(
        state: &mut Self::StorageState,
    ) -> Self::LockResult<Self::ATGuard<'_>>;

    /// Releases the specified memory region back to the allocation tracker.
    fn free_region(
        tracker: Self::LockResult<Self::ATGuard<'_>>,
        base: Self::LockResult<BaseAddress>,
        range: ByteRange,
    ) -> Option<*mut ()>;

    /// Marks reference state as no longer being borrowed.
    fn unborrow_ref<T: ?Sized>(_state: &Self::RefState<T>, _kind: BorrowKind) {}
}

impl<A: ManageMemory> ImplReferencing<A> for ImplDefault {
    type RefState<T: ?Sized> = Rc<ReferenceState<T, Self, A>>;
    type BorrowLock = Cell<BorrowState>;
    type ReadGuard<'a> = ();
    type WriteGuard<'a> = ();
    type StorageState = Rc<MemoryState<Self, A>>;

    #[inline]
    fn get_allocation_tracker(
        state: &mut Self::StorageState,
    ) -> Self::LockResult<Self::ATGuard<'_>> {
        state.tracker.borrow_mut()
    }

    fn free_region(
        mut tracker: Self::LockResult<Self::ATGuard<'_>>,
        base: Self::LockResult<BaseAddress>,
        range: ByteRange,
    ) -> Option<*mut ()> {
        tracker.release(range);
        range.offset_base(base)
    }

    fn unborrow_ref<T: ?Sized>(state: &Self::RefState<T>, _kind: BorrowKind) {
        let next = match state.borrow_kind.get() {
            BorrowState::Read(count) => BorrowState::Read(count - 1),
            BorrowState::Write => BorrowState::Read(0),
        };
        state.borrow_kind.set(next)
    }
}

#[cfg(feature = "sync_impl")]
impl<A: ManageMemory> ImplReferencing<A> for ImplConcurrent {
    type RefState<T: ?Sized> = Arc<ReferenceState<T, Self, A>>;
    type BorrowLock = RwLock<()>;
    type ReadGuard<'a> = RwLockReadGuard<'a, ()>;
    type WriteGuard<'a> = RwLockWriteGuard<'a, ()>;
    type StorageState = Arc<MemoryState<Self, A>>;

    #[inline]
    fn try_get_base(base: &Self::Base) -> Self::LockResult<BaseAddress> {
        base.try_read_named(LockTarget::BaseAddress)
            .map(|result| *result)
    }

    #[inline]
    fn get_allocation_tracker(
        state: &mut Self::StorageState,
    ) -> Self::LockResult<Self::ATGuard<'_>> {
        state.tracker.lock_named(LockTarget::AllocationTracker)
    }

    fn free_region(
        tracker: Self::LockResult<Self::ATGuard<'_>>,
        base: Self::LockResult<BaseAddress>,
        range: ByteRange,
    ) -> Option<*mut ()> {
        if let Ok(mut lock) = tracker {
            lock.release(range);

            if let Ok(base) = base {
                range.offset_base(base)
            } else {
                None
            }
        } else {
            None
        }
    }
}
