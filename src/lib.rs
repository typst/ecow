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
    // Must always point to a valid header.
    ptr: NonNull<Header>,
    // For variance.
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
    refs: AtomicUsize::new(0),
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

    /// The number of elements in the vector.
    pub fn len(&self) -> usize {
        self.header().len
    }

    /// Returns `true` if the vector contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Extracts a slice containing the entire vector.
    pub fn as_slice(&self) -> &[T] {
        unsafe { std::slice::from_raw_parts(self.data(), self.len()) }
    }

    /// Extracts a mutable slice containing the entire vector.
    pub fn as_mut_slice(&mut self) -> &[T] {
        unsafe { std::slice::from_raw_parts_mut(self.data_mut(), self.len()) }
    }

    /// Push a value in the vector.
    pub fn push(&mut self, value: T) {
        let len = self.len();
        let capacity = self.capacity();
        if len == capacity {
            self.reserve(1);
        }

        unsafe {
            ptr::write(self.data_mut().add(len), value);
            self.header_mut().len += 1;
        }
    }

    /// How many elements the vector's backing allocation can hold.
    ///
    /// Even if `len == capacity`, pushing into the vector may still
    /// allocate if the reference count is larger than one.
    pub fn capacity(&self) -> usize {
        self.header().capacity
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
}

impl<T> EcoVec<T> {
    /// Grow the capacity to at least the `target` size.
    fn grow(&mut self, target: usize) {
        let layout = Self::layout(target);
        unsafe {
            let ptr = if self.is_allocated() {
                alloc::realloc(
                    self.ptr.as_ptr() as *mut u8,
                    Self::layout(self.capacity()),
                    Self::size(target),
                )
            } else {
                alloc::alloc(layout)
            };

            if ptr.is_null() {
                alloc::handle_alloc_error(layout);
            }

            self.ptr = NonNull::new_unchecked(ptr as *mut Header);
            self.header_mut().capacity = target;
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
    fn header_mut(&mut self) -> &mut Header {
        // Safety: The `data` pointer always points to a valid header, even
        // if the vector is empty.
        unsafe { self.ptr.as_mut() }
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

    /// Whether this vector is backed by an allocation.
    fn is_allocated(&self) -> bool {
        self.ptr.as_ptr() as *const Header != &EMPTY as *const Header
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

#[cold]
fn capacity_overflow() -> ! {
    panic!("capacity overflow");
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vec() {
        let vec: EcoVec<&'static str> = "hello, world! what's going on?"
            .split_whitespace()
            .collect();
        assert_eq!(
            vec.as_slice(),
            &["hello,", "world!", "what's", "going", "on?"]
        );
    }
}
