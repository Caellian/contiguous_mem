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
    memory::ManageMemory,
    raw::{base_addr_layout, BaseAddress},
    types::*,
};

use crate::{memory::SegmentTracker, range::ByteRange, refs::sealed::*, MemoryState};

#[cfg(feature = "sync_impl")]
use crate::error::{LockTarget, LockingError};

/// Implementation details shared between [storage](StorageDetails) and
/// [`reference`](ReferenceDetails) implementations.
pub trait ImplDetails<A: ManageMemory>: Sized {
    /// The type representing the base memory and allocation tracking.
    type Base;
    /// The type representing the segment tracker discrete type.
    type SegmentTracker;
    /// The type representing the segment tracker reference type.
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
    type SegmentTracker = RefCell<SegmentTracker>;
    type ATGuard<'a> = RefMut<'a, SegmentTracker>;
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
    type SegmentTracker = Mutex<SegmentTracker>;
    type ATGuard<'a> = MutexGuard<'a, SegmentTracker>;
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
                <Self as ImplDetails<A>>::get_base(base).unwrap_or(None),
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
    type SegmentTracker = SegmentTracker;
    type ATGuard<'a> = &'a mut SegmentTracker;
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
    type ReadGuard<'a>: core::fmt::Debug;
    /// Type of the concurrent mutable access exclusion write guard.
    type WriteGuard<'a>: core::fmt::Debug;

    /// The type representing reference to internal state
    type StorageState: core::ops::Deref<Target = MemoryState<Self, A>>;

    /// Retrieves the base pointer from the base instance. Non blocking version.
    #[inline]
    fn try_get_base(base: &Self::Base) -> Self::LockResult<BaseAddress> {
        Self::get_base(base)
    }

    /// Returns a writable reference to SegmentTracker.
    fn get_allocation_tracker(
        state: &mut Self::StorageState,
    ) -> Self::LockResult<Self::ATGuard<'_>>;

    /// Releases the specified memory region back to the segment tracker.
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
        state.tracker.lock_named(LockTarget::SegmentTracker)
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

/// Returns [`Pointee`] metadata for provided pair of struct `S` and some
/// unsized type (e.g. a trait) `T`.
///
/// This metadata is usually a pointer to vtable of `T` implementation for
/// `S`, but can be something else and the value is considered internal to
/// the compiler.
#[cfg(feature = "ptr_metadata")]
pub const fn static_metadata<S, T: ?Sized>() -> <T as core::ptr::Pointee>::Metadata
where
    S: core::marker::Unsize<T>,
{
    let (_, metadata) = (core::ptr::NonNull::<S>::dangling().as_ptr() as *const T).to_raw_parts();
    metadata
}

pub(crate) type DropFn = fn(*mut ());
pub(crate) const fn drop_fn<T>() -> fn(*mut ()) {
    if core::mem::needs_drop::<T>() {
        |ptr: *mut ()| unsafe { core::ptr::drop_in_place(ptr as *mut T) }
    } else {
        |_: *mut ()| {}
    }
}

pub(crate) const fn is_layout_valid(size: usize, align: usize) -> bool {
    if !align.is_power_of_two() {
        return false;
    };

    size <= isize::MAX as usize - (align - 1)
}

/// Trait that unifies passing either a [`Layout`] directly or a `&T` where
/// `T: Sized` as an argument to a function which requires a type layout.
pub trait HasLayout {
    /// Returns a layout of the reference or a copy of the layout directly.
    fn as_layout(&self) -> Layout;
}

impl HasLayout for Layout {
    #[inline]
    fn as_layout(&self) -> Layout {
        *self
    }
}

impl<T> HasLayout for &T {
    #[inline]
    fn as_layout(&self) -> Layout {
        Layout::new::<T>()
    }
}
