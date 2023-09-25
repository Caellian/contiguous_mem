#![allow(incomplete_features)]
#![cfg_attr(feature = "no_std", no_std)]
#![cfg_attr(feature = "ptr_metadata", feature(ptr_metadata, unsize))]
#![cfg_attr(feature = "error_in_core", feature(error_in_core))]
#![cfg_attr(feature = "allocator_api", feature(allocator_api))]
#![cfg_attr(doc, feature(doc_auto_cfg))]
#![warn(missing_docs)]
#![doc = include_str!("../doc/crate.md")]

#[cfg(feature = "no_std")]
extern crate alloc;

mod common;
pub mod error;
pub mod range;
mod raw;
pub mod refs;
pub mod tracker;
mod types;

#[cfg(feature = "sync_impl")]
mod sync;
#[cfg(feature = "sync_impl")]
pub use sync::SyncContiguousMemory;

#[cfg(feature = "unsafe_impl")]
mod unsafe_impl;
#[cfg(feature = "unsafe_impl")]
pub use unsafe_impl::UnsafeContiguousMemory;

// Re-exports

/// Memory allocation and management primitives.
pub mod memory {
    pub use crate::raw::{BaseAddress, BasePtr, DefaultMemoryManager, ManageMemory};
}
pub use memory::*;
pub use refs::{CERef, ContiguousEntryRef};
#[cfg(feature = "sync_impl")]
pub use refs::{SCERef, SyncContiguousEntryRef};
#[cfg(feature = "ptr_metadata")]
pub use types::static_metadata;

use core::cell::Cell;
use core::marker::PhantomData;
use core::mem::align_of;
use core::{
    alloc::Layout,
    mem::{size_of, ManuallyDrop},
    ops::Deref,
};

use common::*;
use error::{MemoryError, NoFreeMemoryError};
use range::ByteRange;
use raw::*;
use refs::sealed::{BorrowState, ReferenceState};
use types::*;

/// A memory container for efficient allocation and storage of contiguous data.
///
/// This collection manages a contiguous block of memory, allowing for storage
/// of arbitrary data types while ensuring that stored items are placed
/// adjacently and ensuring they're properly alligned.
///
/// Type argument `Impl` specifies implementation details for the behavior of
/// this struct.
///
/// Note that this structure is a smart abstraction over underlying data,
/// copying it creates a copy which represents the same internal state. If you
/// need to copy the memory region into a new container see:
/// [`ContiguousMemory::copy_data`]
///
/// # Examples
///
/// ```rust
#[doc = include_str!("../examples/default_impl.rs")]
/// ```
#[derive(Clone)]
pub struct ContiguousMemory<A: ManageMemory = DefaultMemoryManager> {
    inner: Rc<MemoryState<ImplDefault, A>>,
}

impl ContiguousMemory {
    /// Creates a new, empty `ContiguousMemory` instance aligned with alignment
    /// of `usize`.
    ///
    /// # Examples
    /// ```rust
    /// # #![allow(unused_mut)]
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut storage = ContiguousMemory::new();
    /// ```
    pub fn new() -> Self {
        Self {
            inner: unsafe {
                MemoryState::new(Layout::from_size_align_unchecked(0, align_of::<usize>()))
                    .expect("unable to create an empty container")
            },
        }
    }

    /// Creates a new `ContiguousMemory` instance with the specified `capacity`,
    /// aligned with alignment of `usize`.
    ///
    /// # Panics
    ///
    /// Panics if capacity exceeds `isize::MAX` bytes or the allocator can't
    /// provide required amount of memory.
    ///
    /// # Examples
    /// ```rust
    /// # #![allow(unused_mut)]
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut storage = ContiguousMemory::with_capacity(1024);
    /// # assert_eq!(storage.capacity(), 1024);
    /// # assert_eq!(storage.align(), core::mem::align_of::<usize>());
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        if !is_layout_valid(capacity, align_of::<usize>()) {
            panic!(
                "capacity too large; max: {}",
                isize::MAX as usize - (align_of::<usize>() - 1)
            )
        }
        Self::with_layout(unsafe {
            Layout::from_size_align_unchecked(capacity, align_of::<usize>())
        })
    }

    /// Creates a new `ContiguousMemory` instance with capacity and alignment of
    /// the provided `layout`.
    ///
    /// # Panics
    ///
    /// Panics if capacity exceeds `isize::MAX` bytes or the allocator can't
    /// provide required amount of memory.
    ///
    /// # Examples
    /// ```rust
    /// # #![allow(unused_mut)]
    /// use core::mem::align_of;
    /// use core::alloc::Layout;
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut storage = ContiguousMemory::with_layout(
    ///     Layout::from_size_align(512, align_of::<u32>()).unwrap()
    /// );
    /// # assert_eq!(storage.capacity(), 512);
    /// # assert_eq!(storage.align(), align_of::<u32>());
    /// ```
    pub fn with_layout(layout: Layout) -> Self {
        Self {
            inner: match MemoryState::new(layout) {
                Ok(it) => it,
                Err(_) => unreachable!("unable to create a container with layout: {:?}", layout),
            },
        }
    }
}

impl<A: ManageMemory> ContiguousMemory<A> {
    /// Creates a new, empty `ContiguousMemory` instance aligned with alignment
    /// of `usize` that uses the specified allocator.
    ///
    /// # Examples
    /// ```rust
    /// # #![allow(unused_mut)]
    /// # use core::mem::align_of;
    /// use contiguous_mem::ContiguousMemory;
    /// use contiguous_mem::memory::DefaultMemoryManager;
    ///
    /// let mut storage = ContiguousMemory::with_alloc(
    ///     DefaultMemoryManager
    /// );
    /// # assert_eq!(storage.capacity(), 0);
    /// # assert_eq!(storage.align(), align_of::<usize>());
    /// ```
    pub fn with_alloc(alloc: A) -> Self {
        unsafe {
            Self {
                inner: MemoryState::new_with_alloc(
                    Layout::from_size_align_unchecked(0, align_of::<usize>()),
                    alloc,
                )
                .expect("unable to create an empty container"),
            }
        }
    }

    /// Creates a new `ContiguousMemory` instance with the specified `capacity`,
    /// aligned with alignment of `usize`.
    ///
    /// # Examples
    /// ```rust
    /// # #![allow(unused_mut)]
    /// # use core::mem::align_of;
    /// use contiguous_mem::ContiguousMemory;
    /// use contiguous_mem::memory::DefaultMemoryManager;
    ///
    /// let mut storage = ContiguousMemory::with_capacity_and_alloc(
    ///     256,
    ///     DefaultMemoryManager
    /// );
    /// # assert_eq!(storage.capacity(), 256);
    /// # assert_eq!(storage.align(), align_of::<usize>());
    /// ```
    pub fn with_capacity_and_alloc(capacity: usize, alloc: A) -> Self {
        if !is_layout_valid(capacity, align_of::<usize>()) {
            panic!(
                "capacity too large; max: {}",
                isize::MAX as usize - (align_of::<usize>() - 1)
            )
        }
        unsafe {
            Self::with_layout_and_alloc(
                Layout::from_size_align_unchecked(capacity, align_of::<usize>()),
                alloc,
            )
        }
    }

    /// Creates a new `ContiguousMemory` instance with capacity and alignment of
    /// the provided `layout`.
    ///
    /// # Panics
    ///
    /// Panics if the provided allocator fails to allocate initial `layout`.
    ///
    /// # Examples
    /// ```rust
    /// # #![allow(unused_mut)]
    /// use core::mem::align_of;
    /// use core::alloc::Layout;
    /// use contiguous_mem::ContiguousMemory;
    /// use contiguous_mem::memory::DefaultMemoryManager;
    ///
    /// let mut storage = ContiguousMemory::with_layout_and_alloc(
    ///     Layout::from_size_align(0, align_of::<u32>()).unwrap(),
    ///     DefaultMemoryManager
    /// );
    /// # assert_eq!(storage.capacity(), 0);
    /// # assert_eq!(storage.align(), align_of::<u32>());
    /// ```
    pub fn with_layout_and_alloc(layout: Layout, alloc: A) -> Self {
        Self {
            inner: match MemoryState::new_with_alloc(layout, alloc) {
                Ok(it) => it,
                Err(_) => panic!("unable to create a container with layout: {:?}", layout),
            },
        }
    }

    /// Returns the base address of the allocated memory.
    ///
    /// # Examples
    /// ```rust
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    /// assert_eq!(s.base(), None);
    ///
    /// let r = s.push(6);
    /// assert_eq!(s.base().is_some(), true);
    /// ```
    #[inline]
    pub fn base(&self) -> BaseAddress {
        self.inner.base.get()
    }

    /// Returns a pointer to the base address of the allocated memory or `null`
    /// if the container didn't allocate.
    ///
    /// # Examples
    /// ```rust
    /// use core::ptr::null;
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    /// assert_eq!(s.base_ptr(), null());
    ///
    /// let r = s.push(3);
    /// assert!(s.base_ptr() != null());
    /// ```
    pub fn base_ptr(&self) -> *const u8 {
        match self.base() {
            Some(it) => it.as_ptr() as *const u8,
            None => core::ptr::null(),
        }
    }

    /// Returns the current capacity (in bytes) of the memory container.
    ///
    /// The capacity represents the size of the memory block that has been
    /// allocated for storing data. It may be larger than the amount of data
    /// currently stored within the container.
    ///
    /// # Examples
    /// ```rust
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    /// assert_eq!(s.capacity(), 0);
    ///
    /// let r1 = s.push(1u8);
    /// assert_eq!(s.capacity(), 1);
    ///
    /// // will add required padding for alignment:
    /// let r2 = s.push(2u32);
    /// assert_eq!(s.capacity(), 8);
    ///
    /// // will fill empty region before r2:
    /// let r3 = s.push(3u8);
    /// let r4 = s.push(4u8);
    /// assert_eq!(s.capacity(), 8);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        match self.base() {
            Some(it) => unsafe { it.as_ref().len() },
            None => 0,
        }
    }

    /// Returns the total size of all stored entries excluding the padding.
    ///
    /// # Examples
    /// ```rust
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    /// assert_eq!(s.size(), 0);
    ///
    /// let r1 = s.push(1u8);
    /// assert_eq!(s.size(), 1);
    ///
    /// // will add required padding for alignment:
    /// let r2 = s.push(2u32);
    /// assert_eq!(s.size(), 5);
    ///
    /// // will fill empty region before r2:
    /// let r3 = s.push(3u8);
    /// let r4 = s.push(4u8);
    /// assert_eq!(s.size(), 7);
    /// ```
    #[inline]
    pub fn size(&self) -> usize {
        self.capacity() - self.inner.tracker.borrow().count_free()
    }

    /// Returns the alignment of the memory container.
    ///
    /// # Examples
    /// ```rust
    /// # #![allow(unused_mut)]
    /// use core::mem::align_of;
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    /// assert_eq!(s.align(), align_of::<usize>());
    /// ```
    #[inline]
    pub fn align(&self) -> usize {
        self.inner.alignment
    }

    /// Returns the layout of the memory region containing stored data.
    ///
    /// # Examples
    /// ```rust
    /// use core::alloc::Layout;
    /// use core::mem::align_of;
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    /// assert_eq!(
    ///     s.layout(),
    ///     Layout::from_size_align(0, align_of::<usize>()).unwrap()
    /// );
    /// let r = s.push(b"Hello world");
    /// assert_eq!(
    ///     s.layout(),
    ///     Layout::from_size_align(8, align_of::<usize>()).unwrap()
    /// );
    /// ```
    #[inline]
    pub fn layout(&self) -> Layout {
        unsafe {
            // SAFETY: Constructor would panic if Layout was invalid.
            base_addr_layout(self.base(), self.align())
        }
    }

    /// Returns `true` if provided generic type `T` can be stored without
    /// growing the container.
    ///
    /// # Examples
    /// ```rust
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    /// assert_eq!(s.can_push_t::<u32>(), false);
    ///
    /// let r1 = s.push(1u32);
    /// assert_eq!(s.can_push_t::<u32>(), false);
    ///
    /// let r2 = s.push(2u32);
    /// let r3 = s.push(3u32);
    /// assert_eq!(s.can_push_t::<u32>(), true);
    /// ```
    pub fn can_push_t<T>(&self) -> bool {
        let layout = Layout::new::<T>();
        let tracker = self.inner.tracker.borrow();
        tracker.peek_next(layout).is_some()
    }

    /// Returns `true` if the provided `value` can be stored without growing the
    /// container.
    ///
    /// `value` can either be a [`Layout`] or a reference to a `Sized` value.
    ///
    /// # Examples
    /// ```rust
    /// use core::alloc::Layout;
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    ///
    /// let r1 = s.push([0u32; 4]);
    ///
    /// let a = [1u32; 2];
    /// assert_eq!(s.can_push(&a), false);
    /// let r2 = s.push(a);
    ///
    /// assert_eq!(s.can_push(Layout::new::<u64>()), true);
    /// ```
    pub fn can_push(&self, value: impl HasLayout) -> bool {
        let layout = value.layout();
        let tracker = self.inner.tracker.borrow();
        tracker.peek_next(layout).is_some()
    }

    /// Grows the memory container to the specified `new_capacity`, optionally
    /// returning the new base address and size of the underlying memory.
    ///
    /// If the base address of the memory block stays the same the returned
    /// value is `None`. If `new_capacity` is 0, the retuned pointer will be an
    /// invalid pointer with container alignment.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` or the allocator
    /// operation fails.
    ///
    /// # Examples
    /// ```rust
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::with_capacity(4);
    /// assert_eq!(s.capacity(), 4);
    /// assert_eq!(s.size(), 0);
    ///
    /// let r = s.push(1u32);
    /// assert_eq!(s.size(), 4);
    /// assert_eq!(s.can_push(&2u32), false);
    ///
    /// s.grow_to(8);
    /// assert_eq!(s.can_push(&2u32), true);
    /// ```
    pub fn grow_to(&mut self, new_capacity: usize) -> Option<BasePtr> {
        match self.try_grow_to(new_capacity) {
            Ok(it) => it,
            Err(MemoryError::Layout(_)) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("allocator error"),
        }
    }

    /// Tries growing the memory container to the specified `new_capacity`,
    /// optionally returning the new base address and size of the underlying
    /// memory, or a [`MemoryError`] if the new capacity exceeds `isize::MAX` or
    /// the allocator can't allocate required memory.
    ///
    /// If the base address of the memory block stays the same the returned
    /// value is `None`.
    ///
    /// # Examples
    /// ```rust
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    ///
    /// assert!(s.try_grow_to(1024).is_ok());
    ///
    /// let el_count: usize = 42;
    /// let el_size: usize = 288230376151711744; // bad read?
    ///
    /// let mut required_size: usize = 1024;
    /// for i in 0..el_count {
    ///     required_size += el_size;
    /// }
    /// assert!(s.try_grow_to(required_size).is_err());
    /// ```
    pub fn try_grow_to(&mut self, new_capacity: usize) -> Result<Option<BasePtr>, MemoryError> {
        let old_capacity = self.capacity();
        let new_capacity = core::cmp::max(old_capacity, new_capacity);
        if new_capacity == old_capacity {
            return Ok(None);
        }

        self.inner.tracker.borrow_mut().grow(new_capacity);

        let old_layout = self.layout();
        let new_layout = Layout::from_size_align(new_capacity, self.inner.alignment)?;

        let prev_base = self.base();
        let new_base = unsafe { self.inner.alloc.grow(prev_base, old_layout, new_layout)? };

        self.inner.base.set(new_base);

        Ok(if new_base != prev_base {
            Some(unsafe {
                // SAFETY: new_capacity must be > 0, because it's max of
                // old_capacity and passed argument, if both are 0 we return
                // early
                new_base.unwrap_unchecked()
            })
        } else {
            None
        })
    }

    /// Grows the underlying memory by `additional` number of bytes.
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + additional`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    ///
    /// # Examples
    /// ```rust
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::with_capacity(4);
    /// assert_eq!(s.capacity(), 4);
    /// assert_eq!(s.size(), 0);
    ///
    /// let r = s.push(1u32);
    /// assert_eq!(s.size(), 4);
    /// assert_eq!(s.can_push(&2u32), false);
    ///
    /// s.reserve(4);
    /// assert_eq!(s.can_push(&2u32), true);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) -> Option<BasePtr> {
        match self.try_reserve(additional) {
            Ok(it) => it,
            Err(MemoryError::Layout(_)) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("unable to allocate more memory"),
        }
    }

    /// Tries growing the underlying memory by `additional` number of bytes,
    /// returning a [`MemoryError`] error if the new capacity exceeds
    /// `isize::MAX` or the allocator can't allocate required memory.
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + additional`.
    ///
    /// # Examples
    /// ```rust
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    ///
    /// assert!(s.try_reserve(1024).is_ok());
    ///
    /// let el_count: usize = 42;
    /// let el_size: usize = 288230376151711744; // bad read?
    ///
    /// let mut required_size: usize = 0;
    /// for i in 0..el_count {
    ///     required_size += el_size;
    /// }
    /// assert!(s.try_reserve(required_size).is_err());
    /// ```
    pub fn try_reserve(&mut self, additional: usize) -> Result<Option<BasePtr>, MemoryError> {
        if additional == 0 {
            return Ok(None);
        }

        let old_capacity = self.capacity();
        let new_capacity = old_capacity.saturating_add(additional);

        self.inner.tracker.borrow_mut().grow(new_capacity);
        let old_layout = self.layout();
        let new_layout = Layout::from_size_align(new_capacity, self.inner.alignment)?;
        let prev_base = self.base();

        let new_base = unsafe {
            self.inner
                .alloc
                .grow(prev_base, old_layout, new_layout)?
                .unwrap_unchecked()
        };

        self.inner.base.set(Some(new_base));

        Ok(if Some(new_base) != prev_base {
            Some(new_base)
        } else {
            None
        })
    }

    /// Reserves additional bytes required to store a value with provided
    /// `layout` while keeping it aligned (required padding bytes at the end of
    /// the container will be included).
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + padding + size_of::<V>()`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve_layout(&mut self, layout: impl HasLayout) -> Option<BasePtr> {
        match self.try_reserve_layout(layout) {
            Ok(it) => it,
            Err(MemoryError::Layout(_)) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("unable to allocate more memory"),
        }
    }

    /// Reserves additional bytes required to store a value with provided
    /// `layout` while keeping it aligned, returning or
    /// a [`MemoryError`] error if
    /// the new capacity exceeds `isize::MAX` or the allocator can't allocate
    /// required memory.
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.get_capacity() + padding + layout.size()`.
    pub fn try_reserve_layout(
        &mut self,
        layout: impl HasLayout,
    ) -> Result<Option<BasePtr>, MemoryError> {
        let layout = layout.layout();
        if layout.size() == 0 {
            return Ok(None);
        }
        match self.base() {
            Some(base) => {
                let last =
                    unsafe { (base.as_ptr() as *mut u8).add(self.inner.tracker.borrow().len()) };
                let align_offset = last.align_offset(layout.align());
                self.try_reserve(align_offset + layout.size())
            }
            None => {
                self.inner.tracker.borrow_mut().grow(layout.size());
                let new_layout = Layout::from_size_align(
                    layout.size(),
                    core::cmp::max(self.inner.alignment, layout.align()),
                )?;

                let new_base = unsafe { self.inner.alloc.allocate(new_layout)?.unwrap_unchecked() };
                self.inner.base.set(Some(new_base));

                Ok(Some(new_base))
            }
        }
    }

    /// Shrinks the capacity with a lower bound and returns the base pointer.
    ///
    /// # Panics
    ///
    /// Panics if the allocator wasn't able to shrink the allocated memory
    /// region.
    pub fn shrink_to(&mut self, new_capacity: usize) -> BaseAddress {
        let mut tracker = self.inner.tracker.borrow_mut();
        let new_capacity = core::cmp::max(tracker.min_len(), new_capacity);
        tracker.shrink(new_capacity);
        let prev_base = self.inner.base.get();

        let old_layout = self.layout();
        if new_capacity == old_layout.size() {
            return prev_base;
        }
        let new_layout = unsafe {
            // SAFETY: Previous layout was valid and had valid alignment,
            // new one is smaller with same alignment so it must be
            // valid as well.
            Layout::from_size_align_unchecked(new_capacity, old_layout.align())
        };

        let new_base = unsafe {
            self.inner
                .alloc
                .shrink(prev_base, self.layout(), new_layout)
        }
        .expect("unable to shrink the container");
        self.inner.base.set(new_base);

        new_base
    }

    /// Shrinks the capacity to fit the currently stored data and returns the
    /// base pointer.
    pub fn shrink_to_fit(&mut self) -> BaseAddress {
        let prev_base = self.inner.base.get();
        let new_capacity = match self.inner.tracker.borrow_mut().shrink_to_fit() {
            Some(it) => it,
            None => return prev_base,
        };
        let old_layout = self.layout();
        let new_layout = unsafe {
            // SAFETY: Previous layout was valid and had valid alignment,
            // new one is smaller with same alignment so it must be
            // valid as well.
            Layout::from_size_align_unchecked(new_capacity, old_layout.align())
        };
        let new_base = unsafe {
            self.inner
                .alloc
                .shrink(prev_base, self.layout(), new_layout)
        }
        .expect("unable to shrink the container");
        self.inner.base.set(new_base);

        new_base
    }

    /// Stores a `value` of type `T` in the contiguous memory block and returns
    /// a [`reference`](ContiguousEntryRef) to it.
    ///
    /// Value type argument `T` is used to infer type size and returned
    /// reference dropping behavior.
    ///
    /// # Panics
    ///
    /// Panics if the collection needs to grow and new capacity exceeds
    /// `isize::MAX` bytes or allocation of additional memory fails.
    pub fn push<T>(&mut self, value: T) -> ContiguousEntryRef<T, A> {
        let mut data = ManuallyDrop::new(value);
        let layout = Layout::for_value(&data);
        let pos = &mut *data as *mut T;

        unsafe { self.push_raw(pos, layout) }
    }

    /// Stores a `value` of type `T` in the contiguous memory block and returns
    /// a reference to it which doesn't mark the memory segment as free when
    /// dropped.
    ///
    /// See [`ContiguousMemory::push`] for details.
    ///
    /// # Panics
    ///
    /// Panics if the collection needs to grow and new capacity exceeds
    /// `isize::MAX` bytes or allocation of additional memory fails.
    pub fn push_persisted<T>(&mut self, value: T) -> ContiguousEntryRef<T, A> {
        let mut data = ManuallyDrop::new(value);
        let layout = Layout::for_value(&data);
        let pos = &mut *data as *mut T;

        unsafe { self.push_raw_persisted(pos, layout) }
    }

    /// Works same as [`push`](ContiguousMemory::push) but takes a `data`
    /// pointer and `layout`.
    ///
    /// Pointer type `T` is used to infer the drop behavior of the returned
    /// reference.
    ///
    /// # Panics
    ///
    /// Panics if the collection needs to grow and new capacity exceeds
    /// `isize::MAX` bytes or allocation of additional memory fails.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it clones memory from provided pointer
    /// which means it could cause a segmentation fault if the pointer is
    /// invalid.
    ///
    /// Further, it also allows escaping type drop glue because it takes type
    /// [`Layout`] as a separate argument.
    ///
    /// # Examples
    ///
    /// Disabling drop handling by casting the provided pointer into `*const ()`
    /// type and then calling [`transmute`](core::mem::transmute) on the
    /// returned reference:
    /// ```rust
    /// # use contiguous_mem::*;
    /// # use core::alloc::Layout;
    /// # use core::mem;
    /// # let mut storage = ContiguousMemory::new();
    /// let value = vec!["ignore", "drop", "for", "me"];
    /// let erased = &value as *const Vec<&str> as *const ();
    /// let layout = Layout::new::<Vec<&str>>();
    ///
    /// // Reference type arguments must be fully specified.
    /// let stored: CERef<Vec<&str>, DefaultMemoryManager> = unsafe {
    ///     mem::transmute(storage.push_raw(erased, layout))
    /// };
    /// ```
    pub unsafe fn push_raw<T>(
        &mut self,
        data: *const T,
        layout: Layout,
    ) -> ContiguousEntryRef<T, A> {
        let mut tracker = self.inner.tracker.borrow_mut();

        let range = loop {
            let base = self.base();
            match tracker.take_next(base, layout) {
                Ok(taken) => {
                    let found = taken.offset_base_unwrap(base);
                    unsafe {
                        core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                    }
                    break taken;
                }
                Err(NoFreeMemoryError) => match base {
                    Some(prev_base) => {
                        let curr_capacity = self.capacity();

                        let start_free =
                            (prev_base.as_ptr() as *const u8).add(tracker.last_offset());
                        let padding = start_free.align_offset(layout.align());
                        let increment = padding + layout.size() - tracker.tailing_free_bytes();

                        let new_capacity = curr_capacity
                            .saturating_mul(2)
                            .max(curr_capacity + increment);

                        tracker.grow(new_capacity);
                        let old_layout = self.layout();
                        let new_layout = Layout::from_size_align(new_capacity, old_layout.align())
                            .expect("new capacity exceeds `isize::MAX`");

                        let new_base = unsafe {
                            self.inner
                                .alloc
                                .grow(Some(prev_base), old_layout, new_layout)
                        }
                        .expect("unable to allocate more memory");
                        self.inner.base.set(new_base);
                    }
                    None => {
                        tracker.grow(layout.size());
                        let new_base = self
                            .inner
                            .alloc
                            .allocate(layout)
                            .expect("pushed element size exceeds `isize::MAX`");
                        self.inner.base.set(new_base);
                    }
                },
            }
        };

        ContiguousEntryRef {
            inner: Rc::new(ReferenceState {
                state: self.inner.clone(),
                range,
                borrow_kind: Cell::new(BorrowState::Read(0)),
                drop_fn: drop_fn::<T>(),
                _phantom: PhantomData,
            }),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }

    /// Variant of [`push_raw`](ContiguousMemory::push_raw) which returns a
    /// reference that doesn't mark the used memory segment as free when
    /// dropped.
    ///
    /// # Panics
    ///
    /// Panics if the collection needs to grow and new capacity exceeds
    /// `isize::MAX` bytes or allocation of additional memory fails.
    pub unsafe fn push_raw_persisted<T>(
        &mut self,
        data: *const T,
        layout: Layout,
    ) -> ContiguousEntryRef<T, A> {
        let value = self.push_raw(data, layout);
        let result = value.clone();
        core::mem::forget(value.inner);
        result
    }

    /// Assumes value is stored at the provided _relative_ `position` in
    /// managed memory and returns a pointer or a reference to it.
    ///
    /// # Safety
    ///
    /// This function isn't unsafe because creating an invalid pointer isn't
    /// considered unsafe. Responsibility for guaranteeing safety falls on
    /// code that's dereferencing the pointer.
    pub fn assume_stored<T>(&self, position: usize) -> ContiguousEntryRef<T, A> {
        ContiguousEntryRef {
            inner: Rc::new(ReferenceState {
                state: self.inner.clone(),
                range: ByteRange(position, position + size_of::<T>()),
                borrow_kind: Cell::new(BorrowState::Read(0)),
                drop_fn: drop_fn::<T>(),
                _phantom: PhantomData,
            }),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }

    /// Clones the allocated memory region into a new MemoryStorage.
    ///
    /// This function isn't unsafe, even though it ignores presence of `Copy`
    /// bound on stored data, because it doesn't create any invalid references.
    #[must_use = "unused copied collection"]
    pub fn copy_data(&self) -> Self
    where
        A: Clone,
    {
        let current_layout = self.layout();
        let result = Self::with_layout_and_alloc(current_layout, self.inner.alloc.clone());
        match self.base() {
            Some(base) => unsafe {
                core::ptr::copy_nonoverlapping(
                    base.as_ptr() as *const (),
                    result.base().unwrap_unchecked().as_ptr() as *mut (),
                    current_layout.size(),
                );
            },
            None => {
                // empty structure; nothing to copy
            }
        }

        result
    }

    /// Marks the entire contents of the container as free, allowing new data
    /// to be stored in place of previously stored data.
    ///
    /// This allows clearing persisted entries created with
    /// [`ContiguousMemory::push_persisted`] and
    /// [`ContiguousMemory::push_raw_persisted`] methods.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it doesn't invalidate any previously
    /// returned references. Storing data into the container and then trying to
    /// access previously stored data from any existing references will cause
    /// undefined behavior.
    pub unsafe fn clear(&mut self) {
        self.inner.tracker.borrow_mut().clear();
    }

    /// Marks the provided `region` of the container as free, allowing new data
    /// to be stored in place of previously stored data.
    ///
    /// This allows clearing persisted entries created with
    /// [`ContiguousMemory::push_persisted`] and
    /// [`ContiguousMemory::push_raw_persisted`] methods.
    ///
    /// # Panics
    ///
    /// This function panics in debug mode if the provided region falls outside
    /// of the memory tracked by the allocation tracker.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it doesn't invalidate any previously
    /// returned references overlapping `region`. Storing data into the
    /// container and then trying to access previously stored data from
    /// overlapping regions will cause undefined behavior.
    pub unsafe fn clear_region(&mut self, region: ByteRange) {
        self.inner.tracker.borrow_mut().release(region);
    }

    /// Forgets this container without dropping it and returns its base address
    /// and [`Layout`].
    ///
    /// # Safety
    ///
    /// Calling this method will create a memory leak because the smart pointer
    /// to state will not be dropped even when all of the created references go
    /// out of scope. As this method takes ownership of the container, calling
    /// it also ensures that dereferencing pointers created by
    /// [`as_ptr`](refs::ContiguousEntryRef::as_ptr) and related
    /// `ContiguousEntryRef` functions is guaranteed to be safe.
    ///
    /// This method isn't unsafe as leaking data doesn't cause undefined
    /// behavior.
    /// ([_see details_](https://doc.rust-lang.org/nomicon/leaking.html))
    pub fn forget(self) -> (BaseAddress, Layout) {
        let base = self.inner.base.get();
        let layout = self.layout();
        core::mem::forget(self);
        (base, layout)
    }
}

#[cfg(feature = "debug")]
impl<A: ManageMemory> core::fmt::Debug for ContiguousMemory<A>
where
    MemoryState<ImplDefault, A>: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ContiguousMemory")
            .field("inner", &self.inner)
            .finish()
    }
}

impl Default for ContiguousMemory {
    fn default() -> Self {
        ContiguousMemory::new()
    }
}

impl<A: ManageMemory + Default> Default for ContiguousMemory<A> {
    fn default() -> Self {
        ContiguousMemory::with_alloc(A::default())
    }
}

#[cfg(all(test, not(feature = "no_std")))]
mod test {
    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq)]
    #[repr(C)]
    struct Person {
        name: String,
        last_name: String,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    #[repr(C)]
    struct Car {
        owner: Person,
        driver: Option<Person>,
        cost: u32,
        miles: u32,
    }

    #[test]
    fn store_and_get() {
        let mut memory = ContiguousMemory::with_capacity(1024);

        let person_a = Person {
            name: "Jerry".to_string(),
            last_name: "Taylor".to_string(),
        };

        let person_b = Person {
            name: "Larry".to_string(),
            last_name: "Taylor".to_string(),
        };

        let car_a = Car {
            owner: person_a.clone(),
            driver: Some(person_b.clone()),
            cost: 20_000,
            miles: 30123,
        };

        let car_b = Car {
            owner: person_b.clone(),
            driver: None,
            cost: 30_000,
            miles: 3780123,
        };

        let value_number = 248169u64;
        let value_string = "This is a test string".to_string();
        let value_byte = 0x41u8;

        let stored_ref_number = memory.push(value_number);
        let stored_ref_car_a = memory.push(car_a.clone());
        let stored_ref_string = memory.push(value_string.clone());

        let stored_ref_byte = memory.push(value_byte);
        let stored_ref_car_b = memory.push(car_b.clone());

        assert_eq!(*stored_ref_number.get(), value_number);
        assert_eq!(*stored_ref_car_a.get(), car_a);
        assert_eq!(*stored_ref_string.get(), value_string);
        assert_eq!(*stored_ref_car_b.get(), car_b);
        assert_eq!(*stored_ref_byte.get(), value_byte);
    }

    #[test]
    fn add_to_zero_sized() {
        let mut memory = ContiguousMemory::new();

        let person = Person {
            name: "Jacky".to_string(),
            last_name: "Larsson".to_string(),
        };

        let stored_person = memory.push(person.clone());

        assert_eq!(memory.capacity(), 48);
        assert_eq!(*stored_person.get(), person);
    }
}
