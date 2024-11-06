#![allow(unused)]

use core::{
    cell::{Cell, RefCell},
    ptr::NonNull,
};

use crate::{
    error::MemoryError,
    memory::{DefaultMemoryManager, ManageMemory, SegmentTracker},
};

use super::*;

/// Pointer to allocated slice of memory.
pub type BasePtr = NonNull<[u8]>;
/// Optional [`BasePtr`] value.
///
/// `None` for zero-sized contiguous memory, `Some` otherwise.
pub type BaseAddress = Option<BasePtr>;

#[cfg_attr(feature = "debug", derive(Debug))]
pub struct MemoryState<Impl: ImplDetails<A>, A: ManageMemory> {
    pub base: Impl::Base,
    pub tracker: Impl::Tracker,
    pub alloc: A,
}

impl<Impl: ImplDetails<DefaultMemoryManager>> MemoryState<Impl, DefaultMemoryManager> {
    pub fn new(layout: Layout) -> Result<Self, MemoryError> {
        let alloc = DefaultMemoryManager;
        let ptr = alloc.allocate(layout)?;
        Ok(MemoryState {
            base: Impl::Base::from(MemoryBase {
                address: ptr,
                alignment: layout.align(),
            }),
            tracker: Impl::Tracker::from(SegmentTracker::new(layout.size())),
            alloc,
        })
    }
}
impl<Impl: ImplDetails<A>, A: ManageMemory> MemoryState<Impl, A> {
    pub fn new_with_alloc(layout: Layout, alloc: A) -> Result<Self, MemoryError> {
        let ptr = alloc.allocate(layout)?;
        Ok(MemoryState {
            base: Impl::Base::from(MemoryBase {
                address: ptr,
                alignment: layout.align(),
            }),
            tracker: Impl::Tracker::from(SegmentTracker::new(layout.size())),
            alloc,
        })
    }
}

impl<Impl: ImplDetails<A>, A: ManageMemory + Clone> Clone for MemoryState<Impl, A> {
    fn clone(&self) -> Self {
        MemoryState {
            base: Impl::Base::from(*ReadableInner::read(&self.base).unwrap()),
            tracker: Impl::Tracker::from(ReadableInner::read(&self.tracker).unwrap().clone()),
            alloc: self.alloc.clone(),
        }
    }
}

impl<Impl: ImplDetails<A>, A: ManageMemory> Drop for MemoryState<Impl, A> {
    fn drop(&mut self) {
        if let Ok(base) = ReadableInner::read(&self.base) {
            unsafe { A::deallocate(&self.alloc, *base) }
        }
    }
}

/// Memory allocation details.
///
/// Unlike a fat pointer, this struct also stores information on expected
/// alignment the slice was allocated with, unifying [`Layout`] and pointer
/// types.
#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct MemoryBase {
    pub(crate) address: BaseAddress,
    alignment: usize,
}

impl MemoryBase {
    /// Returns a const raw pointer to the first byte or `null` if not
    /// allocated.
    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        self.address
            .map(|it| it.as_ptr() as *const u8)
            .unwrap_or_else(core::ptr::null)
    }
    /// Returns a const raw pointer to the first byte.
    ///
    /// # Safety
    ///
    /// This method assumes the base address exists (has been allocated).
    /// Calling it is UB if the slice wasn't yet allocated.
    #[inline]
    pub unsafe fn as_ptr_unchecked<T>(&self) -> *const T {
        self.address.unwrap_unchecked().as_ptr() as *const T
    }

    /// Returns a mutable raw pointer to the first byte or `null` if not
    /// allocated.
    #[inline]
    pub fn as_ptr_mut(&self) -> *mut u8 {
        self.address
            .map(|it| it.as_ptr() as *mut u8)
            .unwrap_or_else(core::ptr::null_mut)
    }

    /// Returns a mutable raw pointer to the first byte.
    ///
    /// # Safety
    ///
    /// This method assumes the base address exists (slice has been allocated).
    /// Calling it is UB if the slice wasn't yet allocate.
    #[inline]
    pub unsafe fn as_ptr_mut_unchecked<T>(&self) -> *mut T {
        self.address.unwrap_unchecked().as_ptr() as *mut T
    }

    /// Returns the absolute position of the slice in memory or 0 if not
    /// allocated.
    #[inline]
    pub fn as_pos(&self) -> usize {
        self.as_ptr() as usize
    }

    /// Returns the absolute position of the slice in memory or targeted
    /// alignment if not allocated.
    #[inline]
    pub fn pos_or_align(&self) -> usize {
        self.address
            .map(|it| it.as_ptr() as *const u8 as usize)
            .unwrap_or(self.alignment)
    }

    /// Returns `true` if the slice has been allocated.
    #[inline]
    pub fn is_allocated(&self) -> bool {
        self.address.is_some()
    }

    /// Returns the size of the allocation, or 0 if the slice hasn't been
    /// allocated.
    #[inline]
    pub fn size(&self) -> usize {
        match self.address {
            Some(it) => unsafe { it.as_ref().len() },
            None => 0,
        }
    }

    /// Returns the (tageted) alignment of the memory slice.
    #[inline]
    pub fn alignment(&self) -> usize {
        self.alignment
    }

    /// Returns the layout of the memory slice.
    #[inline]
    pub fn layout(&self) -> Layout {
        unsafe { Layout::from_size_align_unchecked(self.size(), self.alignment) }
    }
}

unsafe impl Send for MemoryBase {}
unsafe impl Sync for MemoryBase {}
