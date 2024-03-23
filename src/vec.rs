//! A clone-on-write alternative to [`Vec`].

use core::alloc::Layout;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::{self, Debug, Formatter};
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem;
use core::ops::Deref;
use core::ptr::{self, NonNull};

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

use crate::sync::atomic::{self, AtomicUsize, Ordering::*};

/// Create a new [`EcoVec`] with the given elements.
/// ```
/// # use ecow::eco_vec;
/// assert_eq!(eco_vec![1; 4], [1; 4]);
/// assert_eq!(eco_vec![1, 2, 3], [1, 2, 3]);
/// ```
#[macro_export]
macro_rules! eco_vec {
    () => { $crate::EcoVec::new() };
    ($elem:expr; $n:expr) => { $crate::EcoVec::from_elem($elem, $n) };
    ($($value:expr),+ $(,)?) => { $crate::EcoVec::from([$($value),+]) };
}

/// An economical vector with clone-on-write semantics.
///
/// This type has the same layout as a slice `&[T]`: It consists of a pointer
/// and a length. The pointer is null-pointer optimized (meaning that
///  [`Option<EcoVec<T>>`] has the same size as `EcoVec<T>`). Dereferencing an
/// `EcoVec` to a slice is a no-op.
///
/// Within its allocation, an `EcoVec` stores a reference count and its
/// capacity. In contrast to an [`Arc<Vec<T>>`](alloc::sync::Arc), it only
/// requires a single allocation for both the reference count and the elements.
/// The internal reference counter is atomic, making this type [`Sync`] and
/// [`Send`].
///
/// Note that most mutating methods require [`T: Clone`](Clone) due to
/// clone-on-write semantics.
///
/// # Example
/// ```
/// use ecow::EcoVec;
///
/// // Empty vector does not allocate, but first push does.
/// let mut first = EcoVec::new();
/// first.push(1);
/// first.push(2);
/// assert_eq!(first, [1, 2]);
///
/// // This clone is cheap, it references the same allocation.
/// let mut second = first.clone();
///
/// // This makes a real copy (clone-on-write).
/// second.push(3);
/// assert_eq!(second, [1, 2, 3]);
///
/// // As `second` was cloned upon mutation, this iterator can
/// // move the elements. If the allocation was still shared with
/// // `first`, this would clone lazily.
/// assert_eq!(second.into_iter().collect::<Vec<_>>(), vec![1, 2, 3]);
/// ```
#[repr(C)]
pub struct EcoVec<T> {
    /// Is `Self::dangling()` when the vector is unallocated.
    ///
    /// Otherwise, points `Self::offset()` bytes after a valid allocation and
    /// header, to the start of the vector's elements. It is then aligned to the
    /// maximum of the header's alignment and T's alignment. The pointer is
    /// valid for `len` reads and `capacity` writes of T. The elements may only
    /// be accessed mutably if the reference-count is `1`.
    ptr: NonNull<T>,
    /// The number of elements in the vector.
    ///
    /// Invariant: `len <= capacity`.
    len: usize,
    /// See Vec's impl for more details.
    phantom: PhantomData<T>,
}

/// The start of the backing allocation.
///
/// This is followed by padding, if necessary, and then the actual data.
#[derive(Debug)]
struct Header {
    /// The vector's reference count. Starts at 1 and only drops to zero
    /// when the last vector is dropped.
    ///
    /// Invariant: `refs <= isize::MAX`.
    refs: AtomicUsize,
    /// The number of elements the backing allocation can hold. Zero if there
    /// is no backing allocation.
    ///
    /// May only be mutated if `refs == 1`.
    ///
    /// Invariant: `capacity <= isize::MAX`.
    capacity: usize,
}

impl<T> EcoVec<T> {
    /// Create a new, empty vector.
    #[inline]
    pub const fn new() -> Self {
        Self {
            ptr: Self::dangling(),
            len: 0,
            phantom: PhantomData,
        }
    }

    /// Create a new, empty vec with at least the specified capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        let mut vec = Self::new();
        if capacity > 0 {
            unsafe {
                // Safety:
                // - The reference count starts at 1.
                // - The capacity starts at 0 and the target capacity is checked
                //   to be `> 0`.
                vec.grow(capacity);
            }
        }
        vec
    }

    /// Returns `true` if the vector contains no elements.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The number of elements in the vector.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// How many elements the vector's backing allocation can hold.
    ///
    /// Even if `len < capacity`, pushing into the vector may still
    /// allocate if the reference count is larger than one.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.header().map_or(0, |header| header.capacity)
    }

    /// Extracts a slice containing the entire vector.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        // Safety:
        // - The pointer returned by `data()` is non-null, well-aligned, and
        //   valid for `len` reads of `T`.
        // - We have the invariant `len <= capacity <= isize::MAX`.
        // - The memory referenced by the slice isn't mutated for the returned
        //   slice's lifetime, because `self` becomes borrowed and even if there
        //   are other vectors referencing the same backing allocation, they are
        //   now allowed to mutate the slice since then the ref-count is larger
        //   than one.
        unsafe { core::slice::from_raw_parts(self.data(), self.len) }
    }

    /// Removes all values from the vector.
    pub fn clear(&mut self) {
        // Nothing to do if it's empty.
        if self.is_empty() {
            return;
        }

        // If there are other vectors that reference the same backing
        // allocation, we just create a new, empty vector.
        if !self.is_unique() {
            // If another vector was dropped in the meantime, this vector could
            // have become unique, but we don't care, creating a new one
            // is safe nonetheless. Note that this runs the vector's drop
            // impl and reduces the ref-count.
            *self = Self::new();
            return;
        }

        unsafe {
            let prev = self.len;
            self.len = 0;

            // Safety:
            // - We set the length to zero first in case a drop panics, so we
            //   leak rather than double dropping.
            // - We have unique ownership of the backing allocation, so we can
            //   keep it and clear it. In particular, no other vector can have
            //   gained shared ownership in the meantime since `is_unique()`,
            //   as this is the only live vector available for cloning and we
            //   hold a mutable reference to it.
            // - The pointer returned by `data_mut()` is valid for `capacity`
            //   writes, we have the invariant `prev <= capacity` and thus,
            //   `data_mut()` is valid for `prev` writes.
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.data_mut(), prev));
        }
    }
}

impl<T: Clone> EcoVec<T> {
    /// Create a new vector with `n` copies of `value`.
    pub fn from_elem(value: T, n: usize) -> Self {
        let mut vec = Self::with_capacity(n);
        for _ in 0..n {
            // Safety: we just called `EcoVec::with_capacity()`
            unsafe { vec.push_unchecked(value.clone()) }
        }
        vec
    }

    /// Produce a mutable slice containing the entire vector.
    ///
    /// Clones the vector if its reference count is larger than 1.
    pub fn make_mut(&mut self) -> &mut [T] {
        // To provide mutable access, we must have unique ownership over the
        // backing allocation.
        self.make_unique();

        // Safety:
        // The reference count is `1` because of `make_unique`.
        // For more details, see `Self::as_slice()`.
        unsafe { core::slice::from_raw_parts_mut(self.data_mut(), self.len) }
    }

    /// Add a value at the end of the vector.
    ///
    /// Clones the vector if its reference count is larger than 1.
    #[inline]
    pub fn push(&mut self, value: T) {
        // Ensure unique ownership and grow the vector if necessary.
        self.reserve((self.len == self.capacity()) as usize);

        // Safety: we just called `EcoVec::reserve()`
        unsafe {
            self.push_unchecked(value);
        }
    }

    /// Add a value at the end of the vector, without reallocating.
    ///
    /// You must ensure that `self.is_unique()` and `self.len < self.capacity()`
    /// hold, by calling `EcoVec::with_capacity()` or `EcoVec::reserve()`.
    #[inline]
    unsafe fn push_unchecked(&mut self, value: T) {
        debug_assert!(self.is_unique());
        debug_assert!(self.len < self.capacity());

        unsafe {
            // Safety:
            // - The caller must ensure that the reference count is `1`.
            // - The pointer returned by `data_mut()` is valid for `capacity`
            //   writes.
            // - The caller must ensure that `len < capacity`.
            // - Thus, `data_mut() + len` is valid for one write.
            ptr::write(self.data_mut().add(self.len), value);

            // Safety:
            // Since we reserved space, we maintain `len <= capacity`.
            self.len += 1;
        }
    }

    /// Removes the last element from a vector and returns it, or `None` if the
    /// vector is empty.
    ///
    /// Clones the vector if its reference count is larger than 1.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        self.make_unique();

        unsafe {
            // Safety:
            // Cannot underflow because `is_empty` returned `false`.
            self.len -= 1;

            // Safety:
            // - The reference count is `1` because of `make_unique`.
            // - The pointer returned by `data()` is valid for `len` reads and
            //   thus `data() + new_len` is valid for one read.
            Some(ptr::read(self.data().add(self.len)))
        }
    }

    /// Inserts an element at an index within the vector, shifting all elements
    /// after it to the right.
    ///
    /// Clones the vector if its reference count is larger than 1.
    ///
    /// Panics if `index > len`.
    pub fn insert(&mut self, index: usize, value: T) {
        if index > self.len {
            out_of_bounds(index, self.len);
        }

        // Ensure unique ownership and grow the vector if necessary.
        self.reserve((self.len == self.capacity()) as usize);

        unsafe {
            // Safety:
            // - The reference count is `1` because of `reserve`.
            // - The pointer returned by `data_mut()` is valid for `len`
            //   reads and `capacity` writes of `T`.
            // - Thus, `at` is valid for `len - index` reads of `T`
            // - And `at` is valid for `capacity - index` writes of `T`.
            //   Because of the `reserve` call, we have `len < capacity` and
            //   thus `at + 1` is valid for `len - index` writes of `T`.
            let at = self.data_mut().add(index);
            ptr::copy(at, at.add(1), self.len - index);

            // Safety:
            // - The pointer returned by `data_mut()` is valid for `capacity`
            //   writes.
            // - Due to the bounds check above, `index <= len`
            // - Due to the reserve check, `len < capacity`.
            // - Thus, `data() + index` is valid for one write.
            ptr::write(at, value);

            // Safety:
            // Since we reserved space, we maintain `len <= capacity`.
            self.len += 1;
        }
    }

    /// Removes and returns the element at position index within the vector,
    /// shifting all elements after it to the left.
    ///
    /// Clones the vector if its reference count is larger than 1.
    ///
    /// Panics if `index >= len`.
    pub fn remove(&mut self, index: usize) -> T {
        if index >= self.len {
            out_of_bounds(index, self.len);
        }

        self.make_unique();

        unsafe {
            // Safety:
            // - The reference count is `1` because of `make_unique`.
            // - The pointer returned by `data()` is valid for `len` reads.
            // - Due to the check above, `index < len`.
            // - Thus, `at` is valid for one read.
            let at = self.data_mut().add(index);
            let value = ptr::read(at);

            // Safety:
            // - The pointer returned by `data()` is valid for `len` reads and
            //   `capacity` writes.
            // - Thus, `at + 1` is valid for `len - index - 1` reads.
            // - Thus, `at` is valid for `capacity - index` writes.
            // - Due to the invariant `len <= capacity`, `at` is also valid
            //   for `len - index - 1` writes.
            ptr::copy(at.add(1), at, self.len - index - 1);

            // Safety:
            // Cannot underflow because `index < len` and thus `len > 0`.
            self.len -= 1;

            value
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// Clones the vector if its reference count is larger than 1.
    ///
    /// Note that this clones the vector even if `f` always returns `false`. To
    /// prevent that, you can first iterate over the vector yourself and then
    /// only call `retain` if your condition is `false` for some element.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        // Modified from: https://github.com/servo/rust-smallvec
        // Copyright (c) 2018 The Servo Project Developers
        let len = self.len;
        let values = self.make_mut();

        let mut del = 0;
        for i in 0..len {
            if !f(&mut values[i]) {
                del += 1;
            } else if del > 0 {
                values.swap(i - del, i);
            }
        }

        if del > 0 {
            self.truncate(len - del);
        }
    }

    /// Shortens the vector, keeping the first `target` elements and dropping
    /// the rest.
    ///
    /// Clones the vector if its reference count is larger than 1 and
    /// `target < len`.
    pub fn truncate(&mut self, target: usize) {
        if target >= self.len {
            return;
        }

        if !self.is_unique() {
            // Safety: Just checked bounds.
            *self = Self::from(unsafe { self.get_unchecked(..target) });
            return;
        }

        let rest = self.len - target;
        unsafe {
            // Safety:
            // - Since `target < len`, we maintain `len <= capacity`.
            self.len = target;

            // Safety:
            // The reference count is `1` because of `make_unique`.
            // - The pointer returned by `data_mut()` is valid for `capacity`
            //   writes.
            // - We have the invariant `len <= capacity`.
            // - Thus, `data_mut() + target` is valid for `len - target` writes.
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                self.data_mut().add(target),
                rest,
            ));
        }
    }

    /// Reserve space for at least `additional` more elements.
    ///
    /// Guarantees that the resulting vector has reference count `1` and space
    /// for `additional` more elements.
    pub fn reserve(&mut self, additional: usize) {
        let capacity = self.capacity();
        let mut target = capacity;

        if additional > capacity - self.len {
            // Reserve at least the `additional` capacity, but also at least
            // double the capacity to ensure exponential growth and finally
            // jump directly to a minimum capacity to prevent frequent
            // reallocation for small vectors.
            target = self
                .len
                .checked_add(additional)
                .unwrap_or_else(|| capacity_overflow())
                .max(2 * capacity)
                .max(Self::min_cap());
        }

        if !self.is_unique() {
            let mut vec = Self::with_capacity(target);
            vec.extend(self.iter().cloned());
            *self = vec;
        } else if target > capacity {
            unsafe {
                // Safety:
                // - The reference count is `1` because of `make_unique`.
                // - The `target` capacity is greater than the current capacity
                //   because `additional > 0`.
                self.grow(target);
            }
        }
    }

    /// Clones and pushes all elements in a slice to the vector.
    pub fn extend_from_slice(&mut self, slice: &[T]) {
        if slice.is_empty() {
            return;
        }

        self.reserve(slice.len());

        for value in slice {
            // Safety:
            // - The reference count is `1` because of `reserve`.
            // - `self.len < self.capacity()` because we reserved space for
            //   `slice.len()` more elements.
            unsafe {
                self.push_unchecked(value.clone());
            }
        }
    }
}

impl<T> EcoVec<T> {
    /// Grow the capacity to at least the `target` size.
    ///
    /// May only be called if:
    /// - the reference count is `1`, and
    /// - `target > capacity` (i.e., this methods grows, it doesn't shrink).
    unsafe fn grow(&mut self, mut target: usize) {
        debug_assert!(self.is_unique());
        debug_assert!(target > self.capacity());

        // Maintain the `capacity <= isize::MAX` invariant.
        if target > isize::MAX as usize {
            capacity_overflow();
        }

        // Directly go to maximum capacity for ZSTs.
        if mem::size_of::<T>() == 0 {
            target = isize::MAX as usize;
        }

        let layout = Self::layout(target);
        let allocation = if !self.is_allocated() {
            // Safety:
            // The layout has non-zero size because `target > 0`.
            alloc::alloc::alloc(layout)
        } else {
            // Safety:
            // - `self.ptr` was allocated before (just checked)
            // - the old block was allocated with the current capacity
            // - `Self::size()` guarantees to return a value that is `> 0`
            //   and rounded up to the nearest multiple of `Self::align()`
            //   does not overflow `isize::MAX`.
            alloc::alloc::realloc(
                self.allocation_mut(),
                Self::layout(self.capacity()),
                Self::size(target),
            )
        };

        if allocation.is_null() {
            alloc::alloc::handle_alloc_error(layout);
        }

        // Construct data pointer by offsetting.
        //
        // Safety:
        // Just checked for null and adding only increases the size. Can't
        // overflow because the `allocation` is a valid pointer to
        // `Self::size(target)` bytes and `Self::offset() < Self::size(target)`.
        self.ptr = NonNull::new_unchecked(allocation.add(Self::offset()).cast());
        debug_assert_ne!(self.ptr, Self::dangling());

        // Safety:
        // The freshly allocated pointer is valid for a write of the header.
        ptr::write(
            allocation.cast::<Header>(),
            Header { refs: AtomicUsize::new(1), capacity: target },
        );
    }

    /// Whether this vector has a backing allocation.
    #[inline]
    fn is_allocated(&self) -> bool {
        !ptr::eq(self.ptr.as_ptr(), Self::dangling().as_ptr())
    }

    /// An immutable pointer to the backing allocation.
    ///
    /// May only be called if `is_allocated` returns `true`.
    #[inline]
    unsafe fn allocation(&self) -> *const u8 {
        debug_assert!(self.is_allocated());
        self.ptr.as_ptr().cast::<u8>().sub(Self::offset())
    }

    /// A mutable pointer to the backing allocation.
    ///
    /// May only be called if `is_allocated` returns `true`.
    #[inline]
    unsafe fn allocation_mut(&mut self) -> *mut u8 {
        debug_assert!(self.is_allocated());
        self.ptr.as_ptr().cast::<u8>().sub(Self::offset())
    }

    /// A reference to the header.
    #[inline]
    fn header(&self) -> Option<&Header> {
        // Safety:
        // If the vector is allocated, there is always a valid header.
        self.is_allocated()
            .then(|| unsafe { &*self.allocation().cast::<Header>() })
    }

    /// The data pointer.
    ///
    /// Returns a pointer that is non-null, well-aligned, and valid for `len`
    /// reads of `T`.
    #[inline]
    fn data(&self) -> *const T {
        self.ptr.as_ptr()
    }

    /// The data pointer, mutably.
    ///
    /// Returns a pointer that is non-null, well-aligned, and valid for
    /// `capacity` writes of `T`.
    ///
    /// May only be called if the reference count is 1.
    #[inline]
    unsafe fn data_mut(&mut self) -> *mut T {
        self.ptr.as_ptr()
    }

    /// The layout of a backing allocation for the given capacity.
    #[inline]
    fn layout(capacity: usize) -> Layout {
        // Safety:
        // - `Self::size(capacity)` guarantees that it rounded up the alignment
        //   does not overflow `isize::MAX`.
        // - Since `Self::align()` is the header's alignment or T's alignment,
        //   it fulfills the requirements of a valid alignment.
        unsafe { Layout::from_size_align_unchecked(Self::size(capacity), Self::align()) }
    }

    /// The size of a backing allocation for the given capacity.
    ///
    /// Always `> 0`. When rounded up to the next multiple of `Self::align()` is
    /// guaranteed to be `<= isize::MAX`.
    #[inline]
    fn size(capacity: usize) -> usize {
        mem::size_of::<T>()
            .checked_mul(capacity)
            .and_then(|size| Self::offset().checked_add(size))
            .filter(|&size| {
                // See `Layout::max_size_for_align` for details.
                size < isize::MAX as usize - Self::align()
            })
            .unwrap_or_else(|| capacity_overflow())
    }

    /// The alignment of the backing allocation.
    #[inline]
    const fn align() -> usize {
        max(mem::align_of::<Header>(), mem::align_of::<T>())
    }

    /// The offset of the data in the backing allocation.
    ///
    /// Always `> 0`. `self.ptr` points to the data and `self.ptr - offset` to
    /// the header.
    #[inline]
    const fn offset() -> usize {
        max(mem::size_of::<Header>(), Self::align())
    }

    /// The sentinel value of `self.ptr`, used to indicate an uninitialized,
    /// unallocated vector. It is dangling (does not point to valid memory) and
    /// has no provenance. As such, it must not be used to read/write/offset.
    /// However, it is well-aligned, so it can be used to create 0-length
    /// slices.
    ///
    /// All pointers to allocated vector elements will be distinct from this
    /// value, because allocated vector elements start `Self::offset()` bytes
    /// into a heap allocation and heap allocations cannot start at 0 (null).
    #[inline]
    const fn dangling() -> NonNull<T> {
        unsafe {
            // Safety: This is the stable equivalent of `core::ptr::invalid_mut`.
            // The pointer we create has no provenance and may not be
            // read/write/offset.
            #[allow(clippy::useless_transmute)]
            let ptr = mem::transmute::<usize, *mut T>(Self::offset());

            // Safety: `Self::offset()` is never 0.
            NonNull::new_unchecked(ptr)
        }
    }

    /// The minimum non-zero capacity.
    #[inline]
    const fn min_cap() -> usize {
        // In the spirit of the `EcoVec`, we choose the cutoff size of T from
        // which 1 is the minimum capacity a bit lower than a standard `Vec`.
        if mem::size_of::<T>() == 1 {
            8
        } else if mem::size_of::<T>() <= 32 {
            4
        } else {
            1
        }
    }
}

impl<T: Clone> EcoVec<T> {
    /// Clones and pushes all elements in a trusted-len iterator to the vector.
    ///
    /// # Safety
    /// `ExactSizeIterator::len` must return the exact length of the iterator.
    pub unsafe fn extend_from_trusted<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        let iter = iter.into_iter();
        let count = iter.len();

        if count == 0 {
            return;
        }

        self.reserve(count);

        for value in iter {
            // Safety:
            // - The reference count is `1` because of `reserve`.
            // - `self.len < self.capacity()` because we reserved space for
            //   `slice.len()` more elements.
            unsafe {
                self.push_unchecked(value);
            }
        }
    }

    /// Ensure that this vector has a unique backing allocation.
    ///
    /// May change the capacity.
    fn make_unique(&mut self) {
        if !self.is_unique() {
            *self = Self::from(self.as_slice());
        }
    }
}

impl EcoVec<u8> {
    /// Copies from a byte slice.
    #[inline]
    pub(crate) fn extend_from_byte_slice(&mut self, bytes: &[u8]) {
        if bytes.is_empty() {
            return;
        }

        self.reserve(bytes.len());

        unsafe {
            // Safety:
            // - The source slice is valid for `bytes.len()` reads.
            // - The destination is valid for `bytes.len()` more writes due to
            //   the `reserve` call.
            // - The two ranges are non-overlapping because we hold a mutable
            //   reference to `self` and an immutable one to `bytes`.
            ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                self.data_mut().add(self.len),
                bytes.len(),
            );
        }

        self.len += bytes.len();
    }
}

// Safety: Works like `Arc`.
unsafe impl<T: Sync + Send> Sync for EcoVec<T> {}
unsafe impl<T: Sync + Send> Send for EcoVec<T> {}

impl<T> EcoVec<T> {
    /// Whether no other vector is pointing to the same backing allocation.
    ///
    /// This takes a mutable reference because only callers with ownership or a
    /// mutable reference can ensure that the result stays relevant. Potential
    /// callers with a shared reference could read `true` while another shared
    /// reference is cloned on a different thread, bumping the ref-count. By
    /// restricting this callers with mutable access, we ensure that no
    /// uncontrolled cloning is happening in the time between the `is_unique`
    /// call and any subsequent mutation.
    #[inline]
    pub fn is_unique(&mut self) -> bool {
        // See Arc's is_unique() method.
        self.header().map_or(true, |header| header.refs.load(Acquire) == 1)
    }
}

impl<T: Clone> Clone for EcoVec<T> {
    #[inline]
    fn clone(&self) -> Self {
        // If the vector has a backing allocation, bump the ref-count.
        if let Some(header) = self.header() {
            // See Arc's clone impl for details about memory ordering.
            let prev = header.refs.fetch_add(1, Relaxed);

            // See Arc's clone impl details about guarding against incredibly degenerate programs
            if prev > isize::MAX as usize {
                ref_count_overflow(self.ptr, self.len);
            }
        }

        Self { ptr: self.ptr, len: self.len, phantom: PhantomData }
    }
}

impl<T> Drop for EcoVec<T> {
    fn drop(&mut self) {
        // Drop our ref-count. If there was more than one vector before
        // (including this one), we shouldn't deallocate. Nothing to do if there
        // is no header and thus no backing allocation. See Arc's drop impl for
        // details about memory ordering.
        if self
            .header()
            .map_or(true, |header| header.refs.fetch_sub(1, Release) != 1)
        {
            return;
        }

        // See Arc's drop impl for details.
        atomic::fence(Acquire);

        // Ensures that the backing storage is deallocated even if one of the
        // element drops panics.
        struct Dealloc(*mut u8, Layout);

        impl Drop for Dealloc {
            fn drop(&mut self) {
                // Safety: See below.
                unsafe {
                    alloc::alloc::dealloc(self.0, self.1);
                }
            }
        }

        // Safety:
        // The vector has a header, so `self.allocation()` points to an
        // allocation with the layout of current capacity.
        let _dealloc =
            unsafe { Dealloc(self.allocation_mut(), Self::layout(self.capacity())) };

        unsafe {
            // Safety:
            // No other vector references the backing allocation (just checked).
            // For more details, see `Self::as_slice()`.
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.data_mut(), self.len));
        }
    }
}

impl<T> Deref for EcoVec<T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> Borrow<[T]> for EcoVec<T> {
    #[inline]
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> AsRef<[T]> for EcoVec<T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> Default for EcoVec<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Debug> Debug for EcoVec<T> {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<T: Hash> Hash for EcoVec<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl<T: Eq> Eq for EcoVec<T> {}

impl<T: PartialEq> PartialEq for EcoVec<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T: PartialEq> PartialEq<[T]> for EcoVec<T> {
    #[inline]
    fn eq(&self, other: &[T]) -> bool {
        self.as_slice() == other
    }
}

impl<T: PartialEq> PartialEq<&[T]> for EcoVec<T> {
    #[inline]
    fn eq(&self, other: &&[T]) -> bool {
        self.as_slice() == *other
    }
}

impl<T: PartialEq, const N: usize> PartialEq<[T; N]> for EcoVec<T> {
    #[inline]
    fn eq(&self, other: &[T; N]) -> bool {
        self.as_slice() == other
    }
}

impl<T: PartialEq, const N: usize> PartialEq<&[T; N]> for EcoVec<T> {
    #[inline]
    fn eq(&self, other: &&[T; N]) -> bool {
        self.as_slice() == *other
    }
}

impl<T: PartialEq> PartialEq<Vec<T>> for EcoVec<T> {
    #[inline]
    fn eq(&self, other: &Vec<T>) -> bool {
        self.as_slice() == other
    }
}

impl<T: PartialEq> PartialEq<EcoVec<T>> for [T] {
    #[inline]
    fn eq(&self, other: &EcoVec<T>) -> bool {
        self == other.as_slice()
    }
}

impl<T: PartialEq, const N: usize> PartialEq<EcoVec<T>> for [T; N] {
    #[inline]
    fn eq(&self, other: &EcoVec<T>) -> bool {
        self == other.as_slice()
    }
}

impl<T: PartialEq> PartialEq<EcoVec<T>> for Vec<T> {
    #[inline]
    fn eq(&self, other: &EcoVec<T>) -> bool {
        self == other.as_slice()
    }
}

impl<T: Ord> Ord for EcoVec<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<T: PartialOrd> PartialOrd for EcoVec<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

impl<T: Clone> From<&[T]> for EcoVec<T> {
    fn from(slice: &[T]) -> Self {
        let mut vec = Self::new();
        vec.extend_from_slice(slice);
        vec
    }
}

impl<T: Clone, const N: usize> From<[T; N]> for EcoVec<T> {
    fn from(array: [T; N]) -> Self {
        let mut vec = Self::new();
        unsafe {
            // Safety: Array's IntoIter implements `TrustedLen`.
            vec.extend_from_trusted(array);
        }
        vec
    }
}

impl<T: Clone> From<Vec<T>> for EcoVec<T> {
    /// This needs to allocate to change the layout.
    fn from(other: Vec<T>) -> Self {
        let mut vec = Self::new();
        unsafe {
            // Safety: Vec's IntoIter implements `TrustedLen`.
            vec.extend_from_trusted(other);
        }
        vec
    }
}

impl<T: Clone> FromIterator<T> for EcoVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let hint = iter.size_hint().0;
        let mut vec = Self::with_capacity(hint);
        vec.extend(iter);
        vec
    }
}

impl<T: Clone> Extend<T> for EcoVec<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        let iter = iter.into_iter();
        let hint = iter.size_hint().0;
        if hint > 0 {
            self.reserve(hint);
        }
        for value in iter {
            self.push(value);
        }
    }
}

impl<'a, T> IntoIterator for &'a EcoVec<T> {
    type IntoIter = core::slice::Iter<'a, T>;
    type Item = &'a T;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

impl<T: Clone> IntoIterator for EcoVec<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;

    #[inline]
    fn into_iter(mut self) -> Self::IntoIter {
        IntoIter {
            unique: self.is_unique(),
            front: 0,
            back: self.len,
            vec: self,
        }
    }
}

/// An owned iterator over an [`EcoVec`].
///
/// If the vector had a reference count of 1, this moves out of the vector,
/// otherwise it lazily clones.
pub struct IntoIter<T> {
    /// The underlying vector.
    vec: EcoVec<T>,
    /// Whether we have unique ownership over the underlying allocation.
    unique: bool,
    /// How many elements we have already read from the front.
    /// If `unique` is true, these must not be dropped in our drop impl!
    ///
    /// Invariant: `0 <= front <= back`.
    front: usize,
    /// How many elements we have already read from the back.
    /// If `unique` is true, these must not be dropped in our drop impl!
    ///
    /// Invariant: `0 <= back <= len`.
    back: usize,
}

impl<T> IntoIter<T> {
    /// Returns the remaining items of this iterator as a slice.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        unsafe {
            // Safety:
            // - The pointer returned by `data()` is valid for `len` reads.
            // - Since `front <= back <= len`, `data() + front` is valid for
            //   `back - front` reads.
            // - For more details, see `EcoVec::as_slice`.
            core::slice::from_raw_parts(
                self.vec.data().add(self.front),
                self.back - self.front,
            )
        }
    }
}

impl<T: Clone> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        (self.front < self.back).then(|| {
            let prev = self.front;
            self.front += 1;
            if self.unique {
                // Safety:
                // - We have unique ownership over the underlying allocation.
                // - The pointer returned by `data()` is valid for `len` reads.
                // - We know that `prev < self.back <= len`.
                // - We take ownership of the value and don't drop it again
                //   in our drop impl.
                unsafe { ptr::read(self.vec.data().add(prev)) }
            } else {
                // Safety:
                // - We know that `prev < self.back <= len`.
                unsafe { self.vec.get_unchecked(prev).clone() }
            }
        })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.back - self.front;
        (len, Some(len))
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }
}

impl<T: Clone> DoubleEndedIterator for IntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        (self.back > self.front).then(|| {
            self.back -= 1;
            if self.unique {
                // Safety:
                // - We have unique ownership over the underlying allocation.
                // - The pointer returned by `data()` is valid for `len` reads.
                // - We know that `self.back < len` at this point.
                // - We take ownership of the value and don't drop it again
                //   in our drop impl.
                unsafe { ptr::read(self.vec.data().add(self.back)) }
            } else {
                // Safety:
                // - Due to the subtraction, `self.back < len` at this point.
                unsafe { self.vec.get_unchecked(self.back).clone() }
            }
        })
    }
}

impl<T: Clone> ExactSizeIterator for IntoIter<T> {}

impl<T> Drop for IntoIter<T> {
    fn drop(&mut self) {
        if !self.unique || !self.vec.is_allocated() {
            return;
        }

        // Safety:
        // We have unique ownership over the underlying allocation.
        unsafe {
            // Safety:
            // Set len to zero before dropping to prevent double dropping in
            // EcoVec's drop impl in case of panic.
            self.vec.len = 0;

            // Safety:
            // - The elements in `..self.front` and `self.back..` have
            //   already been moved out of the vector. Thus, we only drop
            //   the elements that remain in the middle.
            // - For details about the slicing, see `Self::as_slice()`.
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                self.vec.data_mut().add(self.front),
                self.back - self.front,
            ));
        }
    }
}

impl<T: Debug> Debug for IntoIter<T> {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_tuple("IntoIter").field(&self.as_slice()).finish()
    }
}

#[cold]
fn capacity_overflow() -> ! {
    panic!("capacity overflow");
}

#[cold]
fn ref_count_overflow<T>(ptr: NonNull<T>, len: usize) -> ! {
    // Drop to decrement the ref count to counter the increment in `clone()`
    drop(EcoVec { ptr, len, phantom: PhantomData });
    panic!("reference count overflow");
}

#[cold]
fn out_of_bounds(index: usize, len: usize) -> ! {
    panic!("index is out bounds (index: {index}, len: {len})");
}

// Copy of `std::cmp::max::<usize>()` that is callable in `const` contexts
#[inline]
const fn max(x: usize, y: usize) -> usize {
    if x > y {
        x
    } else {
        y
    }
}

#[cfg(feature = "std")]
impl std::io::Write for EcoVec<u8> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.extend_from_byte_slice(buf);
        Ok(buf.len())
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

#[cfg(feature = "serde")]
mod serde {
    use crate::EcoVec;
    use core::{fmt, marker::PhantomData};
    use serde::de::{Deserializer, Visitor};

    impl<T: serde::Serialize> serde::Serialize for EcoVec<T> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            self.as_slice().serialize(serializer)
        }
    }

    struct EcoVecVisitor<T>(PhantomData<T>);

    impl<'a, T: serde::Deserialize<'a> + Clone> Visitor<'a> for EcoVecVisitor<T> {
        type Value = EcoVec<T>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a sequence")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: serde::de::SeqAccess<'a>,
        {
            let len = seq.size_hint().unwrap_or(0);
            let mut values = EcoVec::with_capacity(len);
            while let Some(value) = seq.next_element()? {
                values.push(value)
            }
            Ok(values)
        }
    }

    impl<'de, T: serde::Deserialize<'de> + Clone> serde::Deserialize<'de> for EcoVec<T> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_seq(EcoVecVisitor(PhantomData))
        }
    }
}
