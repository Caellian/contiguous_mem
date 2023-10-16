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

pub(crate) const unsafe fn null_base(align: usize) -> BasePtr {
    NonNull::new_unchecked(std::mem::transmute((align as *mut u8, 0usize)))
}

/// Returns a `usize` position of base address or panics if it's `None`.
#[inline]
pub(crate) fn base_addr_position(base: BaseAddress) -> usize {
    base.map(|it| it.as_ptr() as *const u8 as usize)
        .expect("base address missing")
}

#[inline]
pub(crate) fn base_addr_capacity(base: BaseAddress) -> usize {
    base.map(|it| unsafe { it.as_ref().len() })
        .unwrap_or_default()
}

#[inline]
pub(crate) unsafe fn base_addr_layout(base: BaseAddress, align: usize) -> Layout {
    Layout::from_size_align_unchecked(base_addr_capacity(base), align)
}

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
            base: Impl::Base::from(
                ReadableInner::read_named(&self.base, LockTarget::BaseAddress)
                    .unwrap()
                    .clone(),
            ),
            tracker: Impl::Tracker::from(
                ReadableInner::read_named(&self.tracker, LockTarget::SegmentTracker)
                    .unwrap()
                    .clone(),
            ),
            alloc: self.alloc.clone(),
        }
    }
}

impl<Impl: ImplDetails<A>, A: ManageMemory> Drop for MemoryState<Impl, A> {
    fn drop(&mut self) {
        if let Ok(base) = ReadableInner::read_named(&self.base, LockTarget::BaseAddress) {
            unsafe { A::deallocate(&self.alloc, base.address, base.layout()) }
        }
    }
}

#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct MemoryBase {
    pub address: BaseAddress,
    alignment: usize,
}

impl MemoryBase {
    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        self.address
            .map(|it| it.as_ptr() as *const u8)
            .unwrap_or_else(core::ptr::null)
    }
    #[inline]
    pub unsafe fn as_ptr_unchecked<T>(&self) -> *const T {
        self.address.unwrap_unchecked().as_ptr() as *const T
    }

    #[inline]
    pub fn as_ptr_mut(&self) -> *mut u8 {
        self.address
            .map(|it| it.as_ptr() as *mut u8)
            .unwrap_or_else(core::ptr::null_mut)
    }

    #[inline]
    pub unsafe fn as_ptr_mut_unchecked<T>(&self) -> *mut T {
        self.address.unwrap_unchecked().as_ptr() as *mut T
    }

    #[inline]
    pub fn as_pos(&self) -> usize {
        self.as_ptr() as usize
    }

    #[inline]
    pub fn pos_or_align(&self) -> usize {
        self.address
            .map(|it| it.as_ptr() as *const u8 as usize)
            .unwrap_or(self.alignment)
    }

    #[inline]
    pub fn size(&self) -> usize {
        match self.address {
            Some(it) => unsafe { it.as_ref().len() },
            None => 0,
        }
    }

    #[inline]
    pub fn alignment(&self) -> usize {
        self.alignment
    }

    #[inline]
    pub fn layout(&self) -> Layout {
        unsafe { Layout::from_size_align_unchecked(self.size(), self.alignment) }
    }
}

unsafe impl Send for MemoryBase {}
unsafe impl Sync for MemoryBase {}
