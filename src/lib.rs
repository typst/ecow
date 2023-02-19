#![allow(unused)]

use std::alloc::{self, Layout};
use std::cmp;
use std::marker::PhantomData;
use std::mem;
use std::ops::Deref;
use std::ptr::{self, NonNull};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

/// A reference-counted thin vector.
///
/// Has a size of one word and is null-pointer optimized (meaning that
/// `Option<EcoVec<T>>` also takes only one word).
pub struct EcoVec<T> {
    /// Must always point to a valid header.
    ///
    /// May only be mutated if it does not point to the EMPTY header, which is
    /// the case if and only if `len > 0`.
    ptr: NonNull<Header>,
    /// For variance.
    phantom: PhantomData<T>,
}

/// The start of the data.
///
/// This is followed by padding, if necessary, and then the actual data.
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
    /// Create an empty eco vec.
    pub fn new() -> Self {
        Self {
            ptr: unsafe { NonNull::new_unchecked(&EMPTY as *const Header as *mut Header) },
            phantom: PhantomData,
        }
    }

    /// Create an empty vec with at least the specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        let mut vec = Self::new();
        vec.grow(capacity);
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
    /// Even if `len == capacity`, pushing into the vector may still
    /// allocate if the reference count is larger than one.
    pub fn capacity(&self) -> usize {
        self.header().capacity
    }

    /// Removes all values from the vector.
    pub fn clear(&mut self) {
        unsafe {
            if !self.is_empty() {
                self.header_mut().len = 0;
            }
            ptr::drop_in_place(self.as_mut_slice());
        }
    }

    /// Reserve space for at least `additional` more elements.
    pub fn reserve(&mut self, additional: usize) {
        let len = self.len();
        let capacity = self.capacity();
        if additional > capacity - len {
            let target = len
                .checked_add(additional)
                .unwrap_or_else(|| capacity_overflow())
                .max(2 * capacity)
                .max(Self::min_cap());
            self.grow(target);
        }
    }

    /// Push a value in the vector.
    pub fn push(&mut self, value: T) {
        let len = self.len();
        if len == self.capacity() {
            self.reserve(1);
        }

        unsafe {
            self.header_mut().len += 1;
            ptr::write(self.data_mut().add(len), value);
        }
    }

    /// Removes the last element from a vector and returns it, or None if the
    /// vector is empty.
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        unsafe {
            let header = self.header_mut();
            let new_len = header.len - 1;
            header.len = new_len;
            Some(ptr::read(self.data().add(new_len)))
        }
    }

    /// Inserts an element at position index within the vector, shifting all
    /// elements after it to the right.
    ///
    /// Panics if `index > len`.
    pub fn insert(&mut self, index: usize, value: T) {
        let len = self.len();
        if len == self.capacity() {
            self.reserve(1);
        }

        if index > len {
            out_of_bounds(index, len);
        }

        unsafe {
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
    /// Panics if `index >= len`.
    pub fn remove(&mut self, index: usize) -> T {
        let len = self.len();
        if index >= len {
            out_of_bounds(index, len);
        }

        unsafe {
            self.header_mut().len - 1;
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
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let len = self.len();
        let values = self.as_mut_slice();
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
    pub fn truncate(&mut self, target: usize) {
        let len = self.len();
        if target < len {
            let rest = len - target;
            unsafe {
                self.header_mut().len = target;
                ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                    self.data_mut().add(target),
                    rest,
                ));
            }
        }
    }

    /// Extracts a slice containing the entire vector.
    pub fn as_slice(&self) -> &[T] {
        unsafe { std::slice::from_raw_parts(self.data(), self.len()) }
    }

    /// Extracts a mutable slice containing the entire vector.
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { std::slice::from_raw_parts_mut(self.data_mut(), self.len()) }
    }
}

impl<T> EcoVec<T> {
    /// Grow the capacity to at least the `target` size.
    fn grow(&mut self, target: usize) {
        let len = self.len();
        let layout = Self::layout(target);
        unsafe {
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

            self.ptr = NonNull::new_unchecked(ptr as *mut Header);
            ptr::write(
                self.ptr.as_ptr(),
                Header {
                    capacity: target,
                    len,
                    refs: AtomicUsize::new(1),
                },
            );
        }
    }
}

impl<T> EcoVec<T> {
    /// A reference to the header.
    fn header(&self) -> &Header {
        // Safety: The `data` pointer always points to a valid header, even
        // if the vector is empty.
        unsafe { self.ptr.as_ref() }
    }

    /// A mutable reference to the header.
    ///
    /// May only be called if `len > 0`.
    unsafe fn header_mut(&mut self) -> &mut Header {
        // Safety: The `data` pointer always points to a valid header.
        self.ptr.as_mut()
    }

    /// The data pointer.
    fn data(&self) -> *const T {
        unsafe {
            let ptr = self.ptr.as_ptr() as *const u8;
            ptr.add(Self::offset()) as *const T
        }
    }

    /// The data pointer, mutably.
    fn data_mut(&mut self) -> *mut T {
        unsafe {
            let ptr = self.ptr.as_ptr() as *mut u8;
            ptr.add(Self::offset()) as *mut T
        }
    }

    /// The layout of a backing allocation for the given capacity.
    fn layout(capacity: usize) -> Layout {
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

impl<T> Deref for EcoVec<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> FromIterator<T> for EcoVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut vec = Self::new();
        vec.extend(iter);
        vec
    }
}

impl<T> Extend<T> for EcoVec<T> {
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
        assert_eq!(&vec[..], &["hello,", "world!", "what's", "going", "on?"]);
        assert_eq!(vec.pop(), Some("on?"));
        assert_eq!(vec.len(), 4);
        assert_eq!(vec.last(), Some(&"going"));
        assert_eq!(vec.remove(1), "world!");
        assert_eq!(vec[1], "what's");
        vec.push("where?");
        vec.insert(1, "wonder!");
        vec.retain(|s| s.starts_with("w"));
        assert_eq!(vec.as_slice(), &["wonder!", "what's", "where?"]);
        vec.truncate(1);
        assert_eq!(vec.last(), vec.first());
    }
}
