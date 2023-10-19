//! Module re-exporting used types and polyfill to help with feature support.

#[cfg(not(feature = "no_std"))]
mod std_imports {
    pub use std::rc::Rc;
}

#[cfg(not(feature = "no_std"))]
pub use std_imports::*;

#[cfg(feature = "no_std")]
mod nostd_imports {
    pub use ::alloc::rc::Rc;

    pub use ::alloc::vec;
    pub use ::alloc::vec::Vec;
}
#[cfg(feature = "no_std")]
pub use nostd_imports::*;

#[cfg(feature = "error_in_core")]
pub use core::error::Error;
use core::{
    cell::UnsafeCell,
    convert::Infallible, alloc::Layout, ops::{Deref, DerefMut},
};
#[cfg(all(not(feature = "error_in_core"), not(feature = "no_std")))]
pub use std::error::Error;

use crate::{reference::{state::ReferenceState, BorrowState, EntryRef}, memory::{ManageMemory, SegmentTracker}, raw::MemoryBase, ConstructReference};

/// Unifies reading behavior from structs that provide inner mutability.
/// 
/// All implemented functions should be `#[inline]`d to ensure that final code
/// behaves as if this abstraction didn't exist.
/// 
/// This allows different [`ContigousMemory`](crate::ContigousMemory)
/// implementation details to use the same code base while staying correct for
/// the strictest one.
pub trait ReadableInner<T: ?Sized> {
    /// Read guard type returned by `read` and `try_read` operations.
    /// 
    /// In case the cell type doesn't provide a guard for operations, a
    /// replacement that updates cell value on `Drop` should be used (such as
    /// [`CellWriteGuard`]).
    type ReadGuard<'a>: Deref<Target = T>
    where
        Self: 'a;
    
    
    #[cfg(not(any(feature = "error_in_core", not(feature = "no_std"))))]
    type BorrowError;
    #[cfg(any(feature = "error_in_core", not(feature = "no_std")))]
    type BorrowError: Error;

    fn read(&self) -> Result<Self::ReadGuard<'_>, Self::BorrowError>;
    fn try_read(&self) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        self.read()
    }
}

/// Unifies writing behavior from structs that provide inner mutability.
/// 
/// See [`ReadableInner`] for more details.
pub trait WritableInner<T: ?Sized>: ReadableInner<T> {
    /// Write guard type returned by `write` and `try_write` operations.
    /// 
    /// In case the cell type doesn't provide a guard for operations, a
    /// replacement that updates cell value on `Drop` should be used (such as
    /// [`CellWriteGuard`]).
    type WriteGuard<'a>: DerefMut<Target = T>
    where
        Self: 'a;

    #[cfg(not(any(feature = "error_in_core", not(feature = "no_std"))))]
    type MutBorrowError;
    #[cfg(any(feature = "error_in_core", not(feature = "no_std")))]
    type MutBorrowError: Error;

    fn write(&self)
        -> Result<Self::WriteGuard<'_>, Self::MutBorrowError>;
    fn try_write(
        &self,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        self.write()
    }
}

impl<T: Copy> ReadableInner<T> for core::cell::Cell<T> {
    type ReadGuard<'a> = Owned<T> 
    where
        Self: 'a;
    type BorrowError = Infallible;

    #[inline]
    fn read(&self) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        Ok(Owned(self.get()))
    }
    #[inline]
    fn try_read(&self) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        Ok(Owned(self.get()))
    }
}

impl<T: Copy> WritableInner<T> for core::cell::Cell<T> {
    type WriteGuard<'a> = CellWriteGuard<'a, T>
    where
        Self: 'a;
    type MutBorrowError = Infallible;

    #[inline]
    fn write(
        &self,
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
    fn read(&self) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        Ok(self.borrow())
    }
}

impl<T: ?Sized> WritableInner<T> for core::cell::RefCell<T> {
    type WriteGuard<'a> = core::cell::RefMut<'a, T>
    where
        Self: 'a;
    type MutBorrowError = core::cell::BorrowMutError;

    #[inline]
    fn write(
        &self,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        Ok(self.borrow_mut())
    }
    #[inline]
    fn try_write(
        &self,
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
    fn read(&self) -> Result<Self::ReadGuard<'_>, Self::BorrowError> {
        unsafe { Ok(&*self.get()) }
    }
}
impl<T: ?Sized> WritableInner<T> for UnsafeCell<T> {
    type WriteGuard<'a> = &'a mut T
    where
        Self: 'a;
    type MutBorrowError = Infallible;

    #[inline]
    fn write(
        &self,
    ) -> Result<Self::WriteGuard<'_>, Self::MutBorrowError> {
        unsafe { Ok(&mut *self.get())}
    }
}

/// A fake [`Reference`]-like wrapper for [unsafe implementation](ImplUnsafe)
/// state.
/// 
/// As a directly owned value doesn't implement a [`Deref`], this wrapper fills
/// that gap so no matter the implementation details, the state wrapper can be
/// dereferenced into inner value.
#[derive(Debug)]
#[repr(transparent)]
#[cfg(feature = "unsafe_impl")]
pub struct Owned<T>(pub(crate) T);
#[cfg(feature = "unsafe_impl")]
impl<T> From<T> for Owned<T> {
    fn from(value: T) -> Self {
        Owned(value)
    }
}
#[cfg(feature = "unsafe_impl")]
impl<T> std::ops::Deref for Owned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
#[cfg(feature = "unsafe_impl")]
impl<T> DerefMut for Owned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Unifies construction and dereferencing of smart pointers.
/// 
/// Provides bounds and requirements for reference-like types (and [`Owned`]) to
/// be passed through [`ReadableInner`] and [`WritableInner`].
pub trait Reference<T>: Deref<Target = T> {
    /// Constructs a new reference from `value`.
    fn new(value: T) -> Self;
}

impl<T> Reference<T> for Rc<T> {
    fn new(value: T) -> Self {
        Rc::new(value)
    }
}
#[cfg(feature = "unsafe_impl")]
impl<T> Reference<T> for Owned<T> {
    fn new(value: T) -> Self {
        Owned(value)
    }
}

/// Provides a guarded access to [`Cell`](core::cell::Cell) value for use via
/// [`ReadableInner`] and [`WritableInner`].
pub struct CellWriteGuard<'a, T: Copy + 'a> {
    parent: &'a core::cell::Cell<T>,
    value: T,
}

impl<'a, T: Copy + 'a> Drop for CellWriteGuard<'a, T> {
    #[inline]
    fn drop(&mut self) {
        self.parent.set(self.value);
    }
}

impl<'a, T: Copy + 'a> Deref for CellWriteGuard<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<'a, T: Copy + 'a> DerefMut for CellWriteGuard<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

pub(crate) mod sealed {
    /// A marker trait to seal implementation of crate traits.
    pub trait Sealed {}
    impl<T: ?Sized> Sealed for T {}
}
pub(crate) use sealed::Sealed;

/// Implementation details shared between [storage](StorageDetails) and
/// [`reference`](ReferenceDetails) implementations.
pub trait ImplDetails<A: ManageMemory>: Sized {
    /// A reference to internal state
    type StateRef<T>: Reference<T>;

    /// A wrapper for [`MemoryBase`].
    type Base: WritableInner<MemoryBase> + From<MemoryBase>;

    /// A wrapper for [`SegmentTracker`].
    type Tracker: WritableInner<SegmentTracker> + From<SegmentTracker>;

    type PushResult<T>: ConstructReference<T, A, Self>;

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
    type Base = std::cell::RefCell<MemoryBase>;
    type Tracker = std::cell::RefCell<SegmentTracker>;
    type PushResult<T> = EntryRef<T, A>;
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
    type Base = std::cell::Cell<MemoryBase>;
    type Tracker = UnsafeCell<SegmentTracker>;
    type PushResult<T> = *mut T;

    const GROW: bool = false;
}

pub trait ImplReferencing<A: ManageMemory>: ImplDetails<A> {
    /// The type handling concurrent mutable access exclusion.
    type BorrowLock: WritableInner<BorrowState>;

    /// A shared reference to data
    type SharedRef<T>: Reference<T> + Clone;

    /// Marks reference state as no longer being borrowed.
    fn unborrow_ref<T: ?Sized>(_state: &Self::SharedRef<ReferenceState<T, Self, A>>) {}
}

impl<A: ManageMemory> ImplReferencing<A> for ImplDefault {
    type BorrowLock = std::cell::Cell<BorrowState>;

    type SharedRef<T> = Rc<T>;

    fn unborrow_ref<T: ?Sized>(state: &Self::SharedRef<ReferenceState<T, Self, A>>) {
        let next = match state.borrow_kind.get() {
            BorrowState::Read(count) => BorrowState::Read(count - 1),
            BorrowState::Write => BorrowState::Read(0),
        };
        state.borrow_kind.set(next)
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
///
/// This trait is sealed to prevent users from implementing it for arbitrary
/// types which would voilate its intention and cause bloat.
pub trait HasLayout: Sealed {
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
