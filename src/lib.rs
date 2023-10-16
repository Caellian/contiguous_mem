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
pub mod memory;
pub mod range;
mod raw;
pub mod reference;
mod types;

// Re-exports
#[cfg(feature = "ptr_metadata")]
pub use common::static_metadata;
pub use error::*;
pub use reference::{CERef, ContiguousEntryRef};
#[cfg(feature = "sync_impl")]
pub use reference::{SCERef, SyncContiguousEntryRef};

use core::cell::Cell;
use core::marker::PhantomData;
use core::mem::align_of;
use core::{
    alloc::Layout,
    mem::{size_of, ManuallyDrop},
};

use common::*;
use memory::{DefaultMemoryManager, ManageMemory};
use range::ByteRange;
use raw::*;
use reference::state::{BorrowState, ReferenceState};
use reference::EntryRef;
use types::*;

/// A memory container for efficient allocation and storage of contiguous data.
///
/// This collection manages a contiguous block of memory, allowing for storage
/// of arbitrary data types while ensuring that stored items are placed
/// adjacently and ensuring they're properly alligned.
///
/// # Examples
///
/// ```
#[doc = include_str!("../examples/default_impl.rs")]
/// ```
pub struct ContiguousMemory<
    Impl: ImplDetails<A> = ImplDefault,
    A: ManageMemory = DefaultMemoryManager,
> {
    inner: Impl::StateRef<MemoryState<Impl, A>>,
}

#[cfg(feature = "sync_impl")]
pub struct SyncContiguousMemory<A: ManageMemory = DefaultMemoryManager> {
    inner: Arc<MemoryState<ImplConcurrent, A>>,
}

impl<Impl: ImplDetails<DefaultMemoryManager>> ContiguousMemory<Impl> {
    /// Creates a new, empty `ContiguousMemory` instance aligned with alignment
    /// of `usize`.
    ///
    /// # Examples
    /// ```
    /// # #![allow(unused_mut)]
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut storage = ContiguousMemory::new();
    /// ```
    pub fn new() -> Self {
        Self {
            inner: Reference::new(
                MemoryState::<Impl, _>::new(unsafe {
                    Layout::from_size_align_unchecked(0, align_of::<usize>())
                })
                .expect("unable to create an empty container"),
            ),
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
    /// ```
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
    /// ```
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
            inner: match MemoryState::<Impl, _>::new(layout) {
                Ok(it) => Reference::new(it),
                Err(_) => unreachable!("unable to create a container with layout: {:?}", layout),
            },
        }
    }
}

#[contiguous_mem_codegen::gen_sync]
impl<Impl: ImplDetails<A>, A: ManageMemory> ContiguousMemory<Impl, A> {
    /// Creates a new, empty `ContiguousMemory` instance aligned with alignment
    /// of `usize` that uses the specified allocator.
    ///
    /// # Examples
    /// ```
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
                inner: Reference::new(
                    MemoryState::<Impl, _>::new_with_alloc(
                        Layout::from_size_align_unchecked(0, align_of::<usize>()),
                        alloc,
                    )
                    .expect("unable to create an empty container"),
                ),
            }
        }
    }

    /// Creates a new `ContiguousMemory` instance with the specified `capacity`,
    /// aligned with alignment of `usize`.
    ///
    /// # Examples
    /// ```
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
    /// ```
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
            inner: match MemoryState::<Impl, _>::new_with_alloc(layout, alloc) {
                Ok(it) => Reference::new(it),
                Err(_) => panic!("unable to create a container with layout: {:?}", layout),
            },
        }
    }

    /// Returns the base address of the allocated memory.
    ///
    /// # Examples
    /// ```
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    /// assert_eq!(s.base(), None);
    ///
    /// let r = s.push(6);
    /// assert_eq!(s.base().is_some(), true);
    /// ```
    pub fn base(&self) -> MemoryBase {
        *ReadableInner::read_named(&self.inner.base, LockTarget::BaseAddress)
            .expect("can't read base")
    }

    /// Returns a pointer to the base address of the allocated memory or `null`
    /// if the container didn't allocate.
    ///
    /// # Examples
    /// ```
    /// use core::ptr::null;
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    /// assert_eq!(s.base_ptr(), null());
    ///
    /// let r = s.push(3);
    /// assert!(s.base_ptr() != null());
    /// ```
    #[inline]
    pub fn base_ptr(&self) -> *const u8 {
        self.base().as_ptr()
    }

    /// Returns the current capacity (in bytes) of the memory container.
    ///
    /// The capacity represents the size of the memory block that has been
    /// allocated for storing data. It may be larger than the amount of data
    /// currently stored within the container.
    ///
    /// # Examples
    /// ```
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
        self.base().size()
    }

    /// Returns the total size of all stored entries excluding the padding.
    ///
    /// # Examples
    /// ```
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
    pub fn size(&self) -> usize {
        self.capacity()
            - ReadableInner::read_named(&self.inner.tracker, LockTarget::SegmentTracker)
                .unwrap()
                .count_free()
    }

    /// Returns the alignment of the memory container.
    ///
    /// # Examples
    /// ```
    /// # #![allow(unused_mut)]
    /// use core::mem::align_of;
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    /// assert_eq!(s.align(), align_of::<usize>());
    /// ```
    #[inline]
    pub fn align(&self) -> usize {
        self.base().alignment()
    }

    /// Returns the layout of the memory region containing stored data.
    ///
    /// # Examples
    /// ```
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
    pub fn layout(&self) -> Layout {
        self.base().layout()
    }

    /// Returns `true` if provided generic type `T` can be stored without
    /// growing the container.
    ///
    /// # Examples
    /// ```
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
    #[inline]
    pub fn can_push_t<T>(&self) -> bool {
        self.can_push(Layout::new::<T>())
    }

    /// Returns `true` if the provided `value` can be stored without growing the
    /// container.
    ///
    /// `value` can either be a [`Layout`] or a reference to a `Sized` value.
    ///
    /// # Examples
    /// ```
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
        let layout = value.as_layout();
        let tracker =
            ReadableInner::read_named(&self.inner.tracker, LockTarget::SegmentTracker).unwrap();
        let base = self.base();
        tracker.can_store(base, layout)
    }

    /// Grows the memory container to the specified `new_capacity`.
    ///
    /// If the base address changed due to reallocation, new [`MemoryBase`] is
    /// returned as `Ok(Some(MemoryBase))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` or the allocator
    /// operation fails.
    ///
    /// # Examples
    /// ```
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
    pub fn grow_to(&mut self, new_capacity: usize) -> Option<MemoryBase> {
        match self.try_grow_to(new_capacity) {
            Ok(it) => it,
            Err(MemoryError::TooLarge) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("allocator error"),
        }
    }

    /// Tries growing the memory container to the specified `new_capacity`.
    ///
    /// If the base address changed due to reallocation, new [`MemoryBase`] is
    /// returned as `Ok(Some(MemoryBase))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// If the new capacity exceeds `isize::MAX` or the allocator couldn't
    /// allocate required memory, a [`MemoryError`] is returned.
    ///
    /// # Examples
    /// ```
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
    pub fn try_grow_to(&mut self, new_capacity: usize) -> Result<Option<MemoryBase>, MemoryError> {
        let mut base =
            WritableInner::write_named(&self.inner.base, LockTarget::BaseAddress).unwrap();

        let old_capacity = base.size();
        let new_capacity =
            WritableInner::write_named(&self.inner.tracker, LockTarget::SegmentTracker)
                .unwrap()
                .grow(new_capacity);
        if new_capacity == old_capacity {
            return Ok(None);
        };

        let old_layout = base.layout();
        let new_layout = Layout::from_size_align(new_capacity, base.alignment())
            .map_err(|_| MemoryError::TooLarge)?;

        let prev_base = *base;
        base.address = unsafe {
            self.inner
                .alloc
                .grow(prev_base.address, old_layout, new_layout)?
        };

        Ok(if base.address != prev_base.address {
            Some(*base)
        } else {
            None
        })
    }

    /// Handles reserving capacity while ensuring appropriate padding.
    #[inline]
    fn ensure_free_section<const EXACT: bool>(
        &mut self,
        required: usize,
        align: Option<usize>,
    ) -> Result<Option<MemoryBase>, MemoryError> {
        let (capacity, last_offset, largest_free, tailing_free) = {
            let tracker =
                ReadableInner::read_named(&self.inner.tracker, LockTarget::SegmentTracker).unwrap();
            (
                tracker.size(),
                tracker.last_offset(),
                tracker.largest_free_range(),
                tracker.tailing_free_bytes(),
            )
        };
        let base_pos = self.base_ptr() as usize;

        if let Some(largest) = largest_free {
            debug_assert!(base_pos != 0);

            let largest_size = align
                .map(|a| largest.offset(base_pos).aligned(a))
                .unwrap_or(largest)
                .len();

            if largest_size >= required {
                return Ok(None);
            }
        }

        let padding = match align {
            None => 0,
            Some(a) => {
                // we know that base + last_offset won't fall out of addressable
                // range because allocator would've already failed by this point
                let pos = if capacity > 0 {
                    base_pos + last_offset
                } else {
                    // if capacity is 0, we didn't allocate and only need to
                    // ensure relative alignment padding
                    self.align()
                };
                let extra = pos % a;

                // if already aligned padding is 0
                if extra > 0 {
                    a - extra
                } else {
                    0
                }
            }
        };

        let mut additional = required + padding - tailing_free;
        if !EXACT {
            additional = core::cmp::max(capacity, additional);
        }

        self.try_grow_to(capacity + additional)
    }

    /// Grows the underlying memory to ensure container has a free segment that
    /// can store `capacity`.
    /// This function might allocate more than requested amount of memory to
    /// reduce number of reallocations.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// After calling this function, new capacity will be greater than:
    /// `self.size() + capacity`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve(&mut self, capacity: usize) -> Option<MemoryBase> {
        match self.try_reserve(capacity) {
            Ok(it) => it,
            Err(MemoryError::TooLarge) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("unable to allocate more memory"),
        }
    }

    /// Tries growing the underlying memory to ensure container has a free
    /// segment that can store `capacity`.
    /// This function might allocate more than requested amount of memory to
    /// reduce number of reallocations.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// If the new capacity exceeds `isize::MAX` or the allocator couldn't
    /// allocate required memory, a [`MemoryError`] is returned.
    ///
    /// After calling this function, new capacity will be greater than:
    /// `self.size() + capacity`.
    pub fn try_reserve(&mut self, capacity: usize) -> Result<Option<MemoryBase>, MemoryError> {
        if capacity == 0 {
            return Ok(None);
        }
        self.ensure_free_section::<false>(capacity, None)
    }

    /// Grows the underlying memory to ensure container has a free segment that
    /// can store `capacity`.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.size() + capacity`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    ///
    /// # Examples
    /// ```
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::with_capacity(4);
    /// assert_eq!(s.capacity(), 4);
    ///
    /// let r = s.push(1u32);
    /// assert_eq!(s.capacity(), s.size());
    /// assert_eq!(s.can_push(&2u32), false);
    ///
    /// s.reserve_exact(4);
    /// assert_eq!(s.capacity(), 8);
    /// assert_eq!(s.can_push(&2u32), true);
    /// ```
    #[inline]
    pub fn reserve_exact(&mut self, capacity: usize) -> Option<MemoryBase> {
        match self.try_reserve_exact(capacity) {
            Ok(it) => it,
            Err(MemoryError::TooLarge) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("unable to allocate more memory"),
        }
    }

    /// Tries growing the underlying memory to ensure container has a free
    /// segment that can store `capacity`.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// If the new capacity exceeds `isize::MAX` or the allocator couldn't
    /// allocate required memory, a [`MemoryError`] is returned.
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.size() + capacity`.
    ///
    /// # Examples
    /// ```
    /// use contiguous_mem::ContiguousMemory;
    ///
    /// let mut s = ContiguousMemory::new();
    ///
    /// assert!(s.try_reserve_exact(1024).is_ok());
    /// assert_eq!(s.capacity(), 1024);
    ///
    /// let el_count: usize = 42;
    /// let el_size: usize = 288230376151711744; // bad read?
    ///
    /// let mut required_size: usize = 0;
    /// for i in 0..el_count {
    ///     required_size += el_size;
    /// }
    /// assert!(s.try_reserve_exact(required_size).is_err());
    /// ```
    pub fn try_reserve_exact(
        &mut self,
        capacity: usize,
    ) -> Result<Option<MemoryBase>, MemoryError> {
        if capacity == 0 {
            return Ok(None);
        }
        self.ensure_free_section::<true>(capacity, None)
    }

    /// Grows the underlying memory to ensure container has a free segment that
    /// can store a value with provided `layout`.
    /// This function might allocate more than requested amount of memory to
    /// reduce number of reallocations.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// After calling this function, new capacity will be greater than:
    /// `self.size() + padding + size_of::<V>()`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve_layout(&mut self, layout: impl HasLayout) -> Option<MemoryBase> {
        match self.try_reserve_layout(layout) {
            Ok(it) => it,
            Err(MemoryError::TooLarge) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("unable to allocate more memory"),
        }
    }

    /// Tries growing the underlying memory to ensure container has a free
    /// segment that can store a value with provided `layout`.
    /// This function might allocate more than requested amount of memory to
    /// reduce number of reallocations.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// If the new capacity exceeds `isize::MAX` or the allocator couldn't
    /// allocate required memory, a [`MemoryError`] is returned.
    ///
    /// After calling this function, new capacity will be greater than:
    /// `self.size() + padding + size_of::<V>()`.
    pub fn try_reserve_layout(
        &mut self,
        layout: impl HasLayout,
    ) -> Result<Option<MemoryBase>, MemoryError> {
        let layout = layout.as_layout();
        if layout.size() == 0 {
            return Ok(None);
        }
        self.ensure_free_section::<false>(layout.size(), Some(layout.align()))
    }

    /// Grows the underlying memory to ensure container has a free segment that
    /// can store a value with provided `layout`.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.size() + padding + size_of::<V>()`.
    ///
    /// # Panics
    ///
    /// Panics if attempting to grow the container to a capacity larger than
    /// `isize::MAX` or the allocator can't allocate required memory.
    #[inline]
    pub fn reserve_layout_exact(&mut self, layout: impl HasLayout) -> Option<MemoryBase> {
        match self.try_reserve_layout_exact(layout) {
            Ok(it) => it,
            Err(MemoryError::TooLarge) => panic!("new capacity exceeds `isize::MAX`"),
            Err(MemoryError::Allocator(_)) => panic!("unable to allocate more memory"),
        }
    }

    /// Tries growing the underlying memory to ensure container has a free
    /// segment that can store a value with provided `layout`.
    ///
    /// If the base address changed due to reallocation, new [`BasePtr`] is
    /// returned as `Ok(Some(BasePtr))`, if base address stayed the same the
    /// result is `Ok(None)`.
    ///
    /// If the new capacity exceeds `isize::MAX` or the allocator couldn't
    /// allocate required memory, a [`MemoryError`] is returned.
    ///
    /// After calling this function, new capacity will be equal to:
    /// `self.size() + padding + layout.size()`.
    pub fn try_reserve_layout_exact(
        &mut self,
        layout: impl HasLayout,
    ) -> Result<Option<MemoryBase>, MemoryError> {
        let layout = layout.as_layout();
        if layout.size() == 0 {
            return Ok(None);
        }
        self.ensure_free_section::<true>(layout.size(), Some(layout.align()))
    }

    /// Shrinks the capacity with a lower bound and returns the base pointer.
    ///
    /// # Panics
    ///
    /// Panics if the allocator wasn't able to shrink the allocated memory
    /// region.
    pub fn shrink_to(&mut self, new_capacity: usize) -> MemoryBase {
        let mut tracker =
            WritableInner::write_named(&self.inner.tracker, LockTarget::SegmentTracker).unwrap();
        let new_capacity = tracker.shrink(new_capacity);
        let mut base =
            WritableInner::write_named(&self.inner.base, LockTarget::BaseAddress).unwrap();

        let old_layout = self.layout();
        if new_capacity == old_layout.size() {
            return *base;
        }
        let new_layout = unsafe {
            // SAFETY: Previous layout was valid and had valid alignment,
            // new one is smaller with same alignment so it must be
            // valid as well.
            Layout::from_size_align_unchecked(new_capacity, old_layout.align())
        };

        base.address = unsafe {
            self.inner
                .alloc
                .shrink(base.address, self.layout(), new_layout)
        }
        .expect("unable to shrink the container");

        *base
    }

    /// Shrinks the capacity to fit the currently stored data and returns the
    /// base pointer.
    pub fn shrink_to_fit(&mut self) -> MemoryBase {
        let mut base =
            WritableInner::write_named(&self.inner.base, LockTarget::BaseAddress).unwrap();
        let new_capacity =
            match WritableInner::write_named(&self.inner.tracker, LockTarget::SegmentTracker)
                .unwrap()
                .shrink_to_fit()
            {
                Some(it) => it,
                None => return *base,
            };
        let old_layout = self.layout();
        let new_layout = unsafe {
            // SAFETY: Previous layout was valid and had valid alignment,
            // new one is smaller with same alignment so it must be
            // valid as well.
            Layout::from_size_align_unchecked(new_capacity, old_layout.align())
        };
        base.address = unsafe {
            self.inner
                .alloc
                .shrink(base.address, self.layout(), new_layout)
        }
        .expect("unable to shrink the container");

        *base
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
    pub fn push<T>(&mut self, value: T) -> Impl::PushResult<T> {
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
    pub fn push_persisted<T>(&mut self, value: T) -> Impl::PushResult<T> {
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
    /// ```
    /// # use contiguous_mem::*;
    /// # use contiguous_mem::memory::DefaultMemoryManager;
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
    pub unsafe fn push_raw<T>(&mut self, data: *const T, layout: Layout) -> Impl::PushResult<T> {
        let range = loop {
            let base = self.base();
            let next = WritableInner::write_named(&self.inner.tracker, LockTarget::SegmentTracker)
                .unwrap()
                .take_next(base.address, layout);

            match next {
                Some(it) => {
                    let found = it.offset_base_unwrap(base.address);
                    unsafe {
                        core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                    }
                    break it;
                }
                None if Impl::GROW => {
                    self.reserve_layout(layout);
                }
                _ => {}
            }
        };

        EntryRef::new(&self.inner, range)
    }

    /// Variant of [`push_raw`](ContiguousMemory::push_raw) which returns a
    /// reference that doesn't mark the used memory segment as free when
    /// dropped.
    ///
    /// # Panics
    ///
    /// Panics if the collection needs to grow and new capacity exceeds
    /// `isize::MAX` bytes or allocation of additional memory fails.
    ///
    /// # Safety
    ///
    /// See: [`ContiguousMemory::push_raw`]
    pub unsafe fn push_raw_persisted<T>(
        &mut self,
        data: *const T,
        layout: Layout,
    ) -> Impl::PushResult<T> {
        let value = self.push_raw(data, layout);
        let result = value.clone();
        core::mem::forget(value);
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
    pub fn assume_stored<T>(&self, position: usize) -> Impl::PushResult<T> {
        EntryRef::new(&self.inner, ByteRange(position, position + size_of::<T>()))
    }

    /// Clones the allocated memory region into a new `MemoryStorage`.
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
        match self.base().address {
            Some(base) => unsafe {
                core::ptr::copy_nonoverlapping(
                    base.as_ptr() as *const (),
                    result.base().as_ptr_mut_unchecked() as *mut (),
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
        WritableInner::write_named(&self.inner.tracker, LockTarget::SegmentTracker)
            .unwrap()
            .clear();
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
    /// of the memory tracked by the segment tracker.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it doesn't invalidate any previously
    /// returned references overlapping `region`. Storing data into the
    /// container and then trying to access previously stored data from
    /// overlapping regions will cause undefined behavior.
    pub unsafe fn clear_region(&mut self, region: ByteRange) {
        WritableInner::write_named(&self.inner.tracker, LockTarget::SegmentTracker)
            .unwrap()
            .release(region);
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
    pub fn forget(self) -> MemoryBase {
        let base = self.base();
        core::mem::forget(self);
        base
    }
}

#[cfg(feature = "debug")]
impl<Impl: ImplDetails<A>, A: ManageMemory> core::fmt::Debug for ContiguousMemory<Impl, A>
where
    Impl::StateRef<MemoryState<Impl, A>>: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ContiguousMemory")
            .field("inner", &self.inner)
            .finish()
    }
}

impl<Impl: ImplDetails<A>, A: ManageMemory> Clone for ContiguousMemory<Impl, A>
where
    Impl::StateRef<MemoryState<Impl, A>>: Clone,
{
    /// Creates a copy which represents the same memory region as this one.
    ///
    /// If you need to copy the memory region of this container into a new one,
    /// use: [`ContiguousMemory::copy_data`]
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<Impl: ImplDetails<DefaultMemoryManager>> Default for ContiguousMemory<Impl> {
    fn default() -> Self {
        ContiguousMemory::new()
    }
}

impl<Impl: ImplDetails<A>, A: ManageMemory + Default> Default for ContiguousMemory<Impl, A> {
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
        let mut memory = ContiguousMemory::<ImplDefault>::with_capacity(1024);

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
        let mut memory = ContiguousMemory::<ImplDefault>::new();

        let person = Person {
            name: "Jacky".to_string(),
            last_name: "Larsson".to_string(),
        };

        let stored_person = memory.push(person.clone());

        assert_eq!(memory.capacity(), 48);
        assert_eq!(*stored_person.get(), person);
    }
}
