//! Implementation details for behavior specialization marker structs.
//!
//! End-users aren't meant to interact with traits defined in this module
//! directly and they exist solely to simplify implementation of
//! [`ContiguousMemoryStorage`](ContiguousMemoryStorage) by erasing
//! type details of different implementations.
//!
//! Any changes to these traits aren't considered a breaking change and won't
//! be reflected in version numbers.

#![allow(private_bounds)]

use core::{
    alloc::Layout,
    cell::{Cell, RefCell, RefMut},
};

use crate::{
    memory::ManageMemory, raw::MemoryBase, reference::EntryRef, types::*, ContiguousEntryRef,
};

use crate::{memory::SegmentTracker, range::ByteRange, reference::state::*};

#[cfg(feature = "sync_impl")]
use crate::error::{LockTarget, LockingError};
#[cfg(feature = "sync_impl")]
use crate::reference::SyncContiguousEntryRef;

/// Implementation details shared between [storage](StorageDetails) and
/// [`reference`](ReferenceDetails) implementations.
pub trait ImplDetails<A: ManageMemory>: Sized {
    /// A referene to internal state
    type StateRef<T>: Reference<T>;

    /// A reference to a resource that must be shareable
    type SharedRef<T>: Reference<T> + Clone;

    /// A wrapper for [`MemoryBase`].
    type Base: WritableInner<MemoryBase> + From<MemoryBase>;

    /// A wrapper for [`SegmentTracker`].
    type Tracker: WritableInner<SegmentTracker> + From<SegmentTracker>;

    type PushResult<T>: EntryRef<Self, A>;

    const GROW: bool = true;
}

/// Implementation that's not thread-safe but performs faster as it avoids
/// mutexes and locks.
///
/// For example usage of default implementation see: [`ContiguousMemory`](crate::ContiguousMemory)
#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ImplDefault;
impl<A: ManageMemory> ImplDetails<A> for ImplDefault {
    type StateRef<T> = Rc<T>;
    type SharedRef<T> = Rc<T>;
    type Base = RefCell<MemoryBase>;
    type Tracker = RefCell<SegmentTracker>;
    type PushResult<T> = ContiguousEntryRef<T, A>;
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
    type StateRef<T> = Arc<T>;
    type SharedRef<T> = Arc<T>;
    type Base = RwLock<MemoryBase>;
    type Tracker = Mutex<SegmentTracker>;
    type PushResult<T> = SyncContiguousEntryRef<T, A>;
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
    type StateRef<T> = Owned<T>;
    type SharedRef<T> = Rc<T>;
    type Base = core::cell::Cell<MemoryBase>;
    type Tracker = core::cell::UnsafeCell<SegmentTracker>;
    type PushResult<T> = *mut T;

    const GROW: bool = false;
}

pub trait ImplReferencing<A: ManageMemory>: ImplDetails<A> {
    /// The type handling concurrent mutable access exclusion.
    type BorrowLock;

    /// Type of the concurrent mutable access exclusion read guard.
    type ReadGuard<'a>: core::fmt::Debug;
    /// Type of the concurrent mutable access exclusion write guard.
    type WriteGuard<'a>: core::fmt::Debug;

    /// Marks reference state as no longer being borrowed.
    fn unborrow_ref<T: ?Sized>(
        _state: &Self::StateRef<ReferenceState<T, Self, A>>,
        _kind: BorrowKind,
    ) {
    }
}

impl<A: ManageMemory> ImplReferencing<A> for ImplDefault {
    type BorrowLock = Cell<BorrowState>;
    type ReadGuard<'a> = ();
    type WriteGuard<'a> = ();

    fn unborrow_ref<T: ?Sized>(
        state: &Self::StateRef<ReferenceState<T, Self, A>>,
        _kind: BorrowKind,
    ) {
        let next = match state.borrow_kind.get() {
            BorrowState::Read(count) => BorrowState::Read(count - 1),
            BorrowState::Write => BorrowState::Read(0),
        };
        state.borrow_kind.set(next)
    }
}

#[cfg(feature = "sync_impl")]
impl<A: ManageMemory> ImplReferencing<A> for ImplConcurrent {
    type BorrowLock = RwLock<()>;
    type ReadGuard<'a> = RwLockReadGuard<'a, ()>;
    type WriteGuard<'a> = RwLockWriteGuard<'a, ()>;
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
