use std::alloc::{self, Layout};
use std::borrow::Borrow;
use std::cmp::{self, Ordering};
use std::fmt::{self, Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem;
use std::ops::Deref;
use std::ptr::{self, NonNull};
use std::sync::atomic::{AtomicUsize, Ordering::*};

/// An economical vector with clone-on-write semantics.
///
/// Has a size of one word and is null-pointer optimized (meaning that
/// `Option<EcoVec<T>>` also takes only one word).
///
/// Mutating methods require `T: Clone` due to clone-on-write semantics.
pub struct EcoVec<T> {
    /// Must always point to a valid header.
    ///
    /// May only be mutated if it does not point to the `EMPTY` header, which is
    /// the case if and only if `len > 0`.
    ptr: NonNull<Header>,
    /// For variance.
    phantom: PhantomData<T>,
}

/// The start of the data.
///
/// This is followed by padding, if necessary, and then the actual data.
#[derive(Debug)]
struct Header {
    refs: AtomicUsize,
    len: usize,
    capacity: usize,
}

/// The header used by a vector without any items.
static EMPTY: Header = Header {
    refs: AtomicUsize::new(1),
    len: 0,
    capacity: 0,
};

impl<T> EcoVec<T> {
    /// Create a new, empty vector.
    pub fn new() -> Self {
        Self {
            // Safety: TODO.
            ptr: unsafe { NonNull::new_unchecked(&EMPTY as *const Header as *mut Header) },
            phantom: PhantomData,
        }
    }

    /// Create a new, empty vec with at least the specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        let mut vec = Self::new();
        unsafe {
            // Safety: TODO.
            vec.grow(capacity);
        }
        vec
    }

    /// Returns `true` if the vector contains no elements.
    pub fn is_empty(&self) -> bool {
        self.ptr.as_ptr() as *const Header == &EMPTY as *const Header
    }

    /// The number of elements in the vector.
    pub fn len(&self) -> usize {
        self.header().len
    }

    /// How many elements the vector's backing allocation can hold.
    ///
    /// Even if `len < capacity`, pushing into the vector may still
    /// allocate if the reference count is larger than one.
    pub fn capacity(&self) -> usize {
        self.header().capacity
    }

    /// Extracts a slice containing the entire vector.
    pub fn as_slice(&self) -> &[T] {
        // Safety: TODO.
        unsafe { std::slice::from_raw_parts(self.data(), self.len()) }
    }

    /// Removes all values from the vector.
    pub fn clear(&mut self) {
        // Nothing to do if it's empty.
        if self.is_empty() {
            return;
        }

        // If there are other vectors that reference the same backing
        // allocation, we drop our ref-count and just create a new, empty
        // vector.
        if self.header().refs.fetch_sub(1, Release) >= 1 {
            *self = Self::new();
            return;
        }

        // We have unique ownership of the backing allocation, so we can keep
        // it and clear it. We also have to bump our ref-count back up.
        unsafe {
            // Safety: TODO.
            self.header().refs.store(1, Release);
            self.header_mut().len = 0;
            ptr::drop_in_place(self.as_mut_slice_unchecked());
        }
    }
}

impl<T: Clone> EcoVec<T> {
    /// Produce a mutable slice containing the entire vector.
    ///
    /// Clones the vector if its reference count is larger than 1.
    pub fn make_mut(&mut self) -> &mut [T] {
        self.make_unique();

        // Safety: TODO.
        unsafe { std::slice::from_raw_parts_mut(self.data_mut(), self.len()) }
    }

    /// Push a value in the vector.
    ///
    /// Clones the vector if its reference count is larger than 1.
    pub fn push(&mut self, value: T) {
        let len = self.len();
        if len == self.capacity() {
            self.reserve(1);
        } else {
            self.make_unique();
        }

        unsafe {
            // Safety: TODO.
            self.header_mut().len += 1;
            ptr::write(self.data_mut().add(len), value);
        }
    }

    /// Removes the last element from a vector and returns it, or `None` if the
    /// vector is empty.
    ///
    /// Clones the vector if its reference count is larger than 1.
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        self.make_unique();

        unsafe {
            // Safety: TODO.
            let header = self.header_mut();
            let new_len = header.len - 1;
            header.len = new_len;
            Some(ptr::read(self.data().add(new_len)))
        }
    }

    /// Inserts an element at position index within the vector, shifting all
    /// elements after it to the right.
    ///
    /// Clones the vector if its reference count is larger than 1.
    ///
    /// Panics if `index > len`.
    pub fn insert(&mut self, index: usize, value: T) {
        let len = self.len();
        if index > len {
            out_of_bounds(index, len);
        }

        if len == self.capacity() {
            self.reserve(1);
        } else {
            self.make_unique();
        }

        unsafe {
            // Safety: TODO.
            self.header_mut().len += 1;
            let at = self.data_mut().add(index);
            if index < len {
                ptr::copy(at, at.add(1), len - index);
            }
            ptr::write(at, value);
        }
    }

    /// Removes and returns the element at position index within the vector,
    /// shifting all elements after it to the left.
    ///
    /// Clones the vector if its reference count is larger than 1.
    ///
    /// Panics if `index >= len`.
    pub fn remove(&mut self, index: usize) -> T {
        let len = self.len();
        if index >= len {
            out_of_bounds(index, len);
        }

        self.make_unique();

        unsafe {
            // Safety: TODO.
            self.header_mut().len -= 1;
            let val = ptr::read(self.data().add(index));
            ptr::copy(
                self.data().add(index + 1),
                self.data_mut().add(index),
                len - index - 1,
            );
            val
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// Clones the vector if its reference count is larger than 1.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let len = self.len();
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

    /// Shortens the vector, keeping the first len elements and dropping the
    /// rest.
    ///
    /// Clones the vector if its reference count is larger than 1 and
    /// `target < len`.
    pub fn truncate(&mut self, target: usize) {
        let len = self.len();
        if target < len {
            let rest = len - target;
            self.make_unique();
            unsafe {
                // Safety: TODO.
                self.header_mut().len = target;
                ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                    self.data_mut().add(target),
                    rest,
                ));
            }
        }
    }

    /// Reserve space for at least `additional` more elements.
    ///
    /// Clones the vector if its reference count is larger than 1 or if the
    /// current capacity isn't already sufficient.
    pub fn reserve(&mut self, additional: usize) {
        self.make_unique();

        let len = self.len();
        let capacity = self.capacity();
        if additional > capacity - len {
            let target = len
                .checked_add(additional)
                .unwrap_or_else(|| capacity_overflow())
                .max(2 * capacity)
                .max(Self::min_cap());

            unsafe {
                // Safety: TODO.
                self.grow(target);
            }
        }
    }
}

impl<T> EcoVec<T> {
    /// Grow the capacity to at least the `target` size.
    ///
    /// May only be called if the reference count is `1`.
    unsafe fn grow(&mut self, target: usize) {
        let len = self.len();
        let layout = Self::layout(target);
        unsafe {
            // Safety: TODO.
            let ptr = if self.is_empty() {
                alloc::alloc(layout)
            } else {
                alloc::realloc(
                    self.ptr.as_ptr() as *mut u8,
                    Self::layout(self.capacity()),
                    Self::size(target),
                )
            };

            if ptr.is_null() {
                alloc::handle_alloc_error(layout);
            }

            // Safety: TODO.
            self.ptr = NonNull::new_unchecked(ptr as *mut Header);
            ptr::write(
                self.ptr.as_ptr(),
                Header {
                    refs: AtomicUsize::new(1),
                    len,
                    capacity: target,
                },
            );
        }
    }

    /// Extracts a mutable slice containing the entire vector without checking
    /// the reference count.
    ///
    /// May only be called if the reference count is at most `1`.
    #[track_caller]
    unsafe fn as_mut_slice_unchecked(&mut self) -> &mut [T] {
        debug_assert!(self.header().refs.load(Relaxed) <= 1);
        std::slice::from_raw_parts_mut(self.data_mut(), self.len())
    }

    /// A reference to the header.
    fn header(&self) -> &Header {
        // Safety: The pointer always points to a valid header, even if the
        // vector is empty.
        unsafe { self.ptr.as_ref() }
    }

    /// A mutable reference to the header.
    ///
    /// May only be called if `is_empty` returns `false`.
    #[track_caller]
    unsafe fn header_mut(&mut self) -> &mut Header {
        // Safety: The pointer always points to a valid header.
        debug_assert!(!self.is_empty());
        self.ptr.as_mut()
    }

    /// The data pointer.
    fn data(&self) -> *const T {
        // Safety: TODO.
        unsafe {
            let ptr = self.ptr.as_ptr() as *const u8;
            ptr.add(Self::offset()) as *const T
        }
    }

    /// The data pointer, mutably.
    fn data_mut(&mut self) -> *mut T {
        // Safety: See the explanation in `data()`.
        unsafe {
            let ptr = self.ptr.as_ptr() as *mut u8;
            ptr.add(Self::offset()) as *mut T
        }
    }

    /// The layout of a backing allocation for the given capacity.
    fn layout(capacity: usize) -> Layout {
        // Safety: TODO.
        unsafe { Layout::from_size_align_unchecked(Self::size(capacity), Self::align()) }
    }

    /// The size of a backing allocation for the given capacity.
    fn size(capacity: usize) -> usize {
        mem::size_of::<T>()
            .checked_mul(capacity)
            .and_then(|size| Self::offset().checked_add(size))
            .unwrap_or_else(|| capacity_overflow())
    }

    /// The alignment of the backing allocation.
    fn align() -> usize {
        cmp::max(mem::align_of::<Header>(), mem::align_of::<T>())
    }

    /// The offset of the backing allocation.
    fn offset() -> usize {
        cmp::max(mem::size_of::<Header>(), Self::align())
    }

    /// The minimum non-zero capacity.
    fn min_cap() -> usize {
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
    /// Ensure that this vector has a unique backing allocation.
    fn make_unique(&mut self) {
        if self.header().refs.load(Relaxed) > 1 {
            *self = self.iter().cloned().collect();
        }
    }
}

unsafe impl<T: Sync> Sync for EcoVec<T> {}
unsafe impl<T: Send> Send for EcoVec<T> {}

impl<T> Drop for EcoVec<T> {
    fn drop(&mut self) {
        // Nothing to do if there are no elements.
        if self.is_empty() {
            return;
        }

        // Drop our ref-count. If there was more than one vector before
        // (including this one), we shouldn't deallocate.
        if self.header().refs.fetch_sub(1, Release) > 1 {
            return;
        }

        unsafe {
            // Safety: No other vector references the backing allocation
            // (just checked) and given that, `as_mut_slice_unchecked` returns
            // a valid slice of initialized values.
            ptr::drop_in_place(self.as_mut_slice_unchecked());

            // Safety: The vector isn't empty, so `self.ptr` points to an
            // allocation with the layout of current capacity.
            alloc::dealloc(self.ptr.as_ptr() as *mut u8, Self::layout(self.capacity()));
        }
    }
}

impl<T> Deref for EcoVec<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> Borrow<[T]> for EcoVec<T> {
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> AsRef<[T]> for EcoVec<T> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> Default for EcoVec<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Debug> Debug for EcoVec<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<T: Clone> Clone for EcoVec<T> {
    fn clone(&self) -> Self {
        // If the vector isn't empty, bump the ref-count.
        if !self.is_empty() {
            // See Arc's clone impl for details about ordering and aborting.
            let prev = self.header().refs.fetch_add(1, Relaxed);
            if prev > isize::MAX as usize {
                std::process::abort();
            }
        }

        Self {
            ptr: self.ptr,
            phantom: PhantomData,
        }
    }
}

impl<T: Hash> Hash for EcoVec<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl<T: Eq> Eq for EcoVec<T> {}

impl<T: PartialEq> PartialEq for EcoVec<T> {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T: PartialEq> PartialEq<[T]> for EcoVec<T> {
    fn eq(&self, other: &[T]) -> bool {
        self.as_slice() == other
    }
}

impl<T: PartialEq, const N: usize> PartialEq<[T; N]> for EcoVec<T> {
    fn eq(&self, other: &[T; N]) -> bool {
        self.as_slice() == other
    }
}

impl<T: PartialEq> PartialEq<Vec<T>> for EcoVec<T> {
    fn eq(&self, other: &Vec<T>) -> bool {
        self.as_slice() == other
    }
}

impl<T: PartialEq> PartialEq<EcoVec<T>> for [T] {
    fn eq(&self, other: &EcoVec<T>) -> bool {
        self == other.as_slice()
    }
}

impl<T: PartialEq, const N: usize> PartialEq<EcoVec<T>> for [T; N] {
    fn eq(&self, other: &EcoVec<T>) -> bool {
        self == other.as_slice()
    }
}

impl<T: PartialEq> PartialEq<EcoVec<T>> for Vec<T> {
    fn eq(&self, other: &EcoVec<T>) -> bool {
        self == other.as_slice()
    }
}

impl<T: Ord> Ord for EcoVec<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_slice().cmp(&other.as_slice())
    }
}

impl<T: PartialOrd> PartialOrd for EcoVec<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_slice().partial_cmp(&other.as_slice())
    }
}

impl<T: Clone> FromIterator<T> for EcoVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut vec = Self::new();
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

impl<T: Clone> From<&[T]> for EcoVec<T> {
    fn from(slice: &[T]) -> Self {
        slice.iter().cloned().collect()
    }
}

#[cold]
fn capacity_overflow() -> ! {
    panic!("capacity overflow");
}

#[cold]
fn out_of_bounds(index: usize, len: usize) -> ! {
    panic!("index is out bounds (index: {index}, len: {len})");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vec() {
        let mut vec: EcoVec<&'static str> = "hello, world! what's going on?"
            .split_whitespace()
            .collect();

        assert_eq!(vec.len(), 5);
        assert_eq!(vec.capacity(), 8);
        assert_eq!(vec, ["hello,", "world!", "what's", "going", "on?"]);
        assert_eq!(vec.pop(), Some("on?"));
        assert_eq!(vec.len(), 4);
        assert_eq!(vec.last(), Some(&"going"));
        assert_eq!(vec.remove(1), "world!");
        assert_eq!(vec.len(), 3);
        assert_eq!(vec[1], "what's");
        vec.push("where?");
        vec.insert(1, "wonder!");
        vec.retain(|s| s.starts_with("w"));
        assert_eq!(vec, ["wonder!", "what's", "where?"]);
        vec.truncate(1);
        assert_eq!(vec.last(), vec.first());
    }

    #[test]
    fn test_vec_clone() {
        let mut vec = EcoVec::new();
        vec.push(1);
        vec.push(2);
        vec.push(3);
        assert_eq!(vec.len(), 3);
        let mut vec2 = vec.clone();
        vec2.push(4);
        assert_eq!(vec2.len(), 4);
        assert_eq!(vec2, [1, 2, 3, 4]);
        assert_eq!(vec, [1, 2, 3]);
    }
}
