//! Traits for types that can be used as reference counts.

use core::sync::atomic::{self, AtomicUsize, Ordering};

/// A type that can be used as a (potentially non-atomic) reference count.
pub trait RefCount {
    /// Create a new reference count, initialised to `count`.
    fn new(count: usize) -> Self;

    /// Load the reference count.
    fn load(&self, order: Ordering) -> usize;

    /// Increment the reference count.
    fn fetch_add(&self, amount: usize, order: Ordering) -> usize;

    /// Decrement the reference count.
    fn fetch_sub(&self, amount: usize, order: Ordering) -> usize;

    /// Insert a fence.
    fn fence(order: Ordering);
}

/// A type that can be used as an atomic reference count.
/// # Safety
/// Types that implement this trait must ensure that their methods do not ignore the `order` argument
pub unsafe trait AtomicRefCount: RefCount {}

impl RefCount for AtomicUsize {
    #[inline(always)]
    fn new(count: usize) -> Self {
        Self::new(count)
    }

    #[inline(always)]
    fn load(&self, order: Ordering) -> usize {
        self.load(order)
    }

    #[inline(always)]
    fn fetch_add(&self, val: usize, order: Ordering) -> usize {
        self.fetch_add(val, order)
    }

    #[inline(always)]
    fn fetch_sub(&self, val: usize, order: Ordering) -> usize {
        self.fetch_sub(val, order)
    }

    #[inline(always)]
    fn fence(order: Ordering) {
        atomic::fence(order)
    }
}

unsafe impl AtomicRefCount for AtomicUsize {}

impl RefCount for usize {
    #[inline(always)]
    fn new(count: usize) -> Self {
        count
    }

    #[inline(always)]
    fn load(&self, _: Ordering) -> usize {
        *self
    }

    #[inline(always)]
    fn fetch_add(&self, amount: usize, _: Ordering) -> usize {
        *self + amount
    }

    #[inline(always)]
    fn fetch_sub(&self, amount: usize, _: Ordering) -> usize {
        *self - amount
    }

    #[inline(always)]
    fn fence(_: Ordering) {}
}
