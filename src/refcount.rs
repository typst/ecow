//! Traits for types that can be used as reference counts.

use core::sync::atomic::{
    self, AtomicU16, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering,
};

/// A type that can be used as a (potentially non-atomic) reference count.
pub trait RefCount {
    /// The maximum signed representation of ths type. Used to check for
    /// overflow after incrementing the reference count.
    const SIGNED_MAX: isize;

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

macro_rules! impl_atomic_refcount {
    ($atomic_ty:ty, $non_atomic_ty:ty, $non_atomic_signed_ty:ty) => {
        impl RefCount for $atomic_ty {
            const SIGNED_MAX: isize = <$non_atomic_signed_ty>::MAX as isize;

            #[inline(always)]
            fn new(count: usize) -> Self {
                Self::new(count as $non_atomic_ty)
            }

            #[inline(always)]
            fn load(&self, order: Ordering) -> usize {
                self.load(order) as usize
            }

            #[inline(always)]
            fn fetch_add(&self, val: usize, order: Ordering) -> usize {
                self.fetch_add(val as $non_atomic_ty, order) as usize
            }

            #[inline(always)]
            fn fetch_sub(&self, val: usize, order: Ordering) -> usize {
                self.fetch_sub(val as $non_atomic_ty, order) as usize
            }

            #[inline(always)]
            fn fence(order: Ordering) {
                atomic::fence(order)
            }
        }

        unsafe impl AtomicRefCount for $atomic_ty {}
    };
}

impl_atomic_refcount!(AtomicUsize, usize, isize);
impl_atomic_refcount!(AtomicU64, u64, i64);
impl_atomic_refcount!(AtomicU32, u32, i32);
impl_atomic_refcount!(AtomicU16, u16, i16);
impl_atomic_refcount!(AtomicU8, u8, i8);

macro_rules! impl_refcount {
    ($ty:ty, $signed_ty:ty) => {
        impl RefCount for $ty {
            const SIGNED_MAX: isize = <$signed_ty>::MAX as isize;

            #[inline(always)]
            fn new(count: usize) -> Self {
                count as Self
            }

            #[inline(always)]
            fn load(&self, _: Ordering) -> usize {
                (*self) as usize
            }

            #[inline(always)]
            fn fetch_add(&self, amount: usize, _: Ordering) -> usize {
                (*self + amount as Self) as usize
            }

            #[inline(always)]
            fn fetch_sub(&self, amount: usize, _: Ordering) -> usize {
                (*self - amount as Self) as usize
            }

            #[inline(always)]
            fn fence(_: Ordering) {}
        }
    };
}

impl_refcount!(usize, isize);
impl_refcount!(u64, i64);
impl_refcount!(u32, i32);
impl_refcount!(u16, i64);
impl_refcount!(u8, i8);
