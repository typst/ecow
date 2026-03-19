//! Ported from the rust standard libaray.
//! Copyright (c) The Rust Project Contributors
//! See NOTICE for full attribution.

use core::ptr;
use core::slice;

use crate::EcoVec;

use super::Drain;

/// A splicing iterator for [`EcoVec`].
///
/// This struct is created by [`EcoVec::splice()`].
/// See its documentation for more.
#[derive(Debug)]
pub struct Splice<'a, I: Iterator + 'a>
where
    // The Clone bound is required here, because the Drop implementation calls
    // methods that require it.
    I::Item: Clone,
{
    pub(crate) drain: Drain<'a, I::Item>,
    pub(crate) replace_with: I,
}

impl<I: Iterator> Iterator for Splice<'_, I>
where
    I::Item: Clone,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.drain.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.drain.size_hint()
    }
}

impl<I: Iterator> DoubleEndedIterator for Splice<'_, I>
where
    I::Item: Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.drain.next_back()
    }
}

impl<I: Iterator> ExactSizeIterator for Splice<'_, I> where I::Item: Clone {}

// See also: [`crate::collections::vec_deque::Splice`].
impl<I: Iterator> Drop for Splice<'_, I>
where
    I::Item: Clone,
{
    fn drop(&mut self) {
        self.drain.by_ref().for_each(drop);
        // At this point draining is done and the only remaining tasks are splicing
        // and moving things into the final place.
        // Which means we can replace the slice::Iter with pointers that won't point to deallocated
        // memory, so that Drain::drop is still allowed to call iter.len(), otherwise it would break
        // the ptr.offset_from_unsigned contract.
        self.drain.iter = [].iter();

        unsafe {
            if self.drain.tail_len == 0 {
                self.drain.vec.as_mut().extend(self.replace_with.by_ref());
                return;
            }

            // First fill the range left by drain().
            if !self.drain.fill(&mut self.replace_with) {
                return;
            }

            // There may be more elements. Use the lower bound as an estimate.
            // FIXME: Is the upper bound a better guess? Or something else?
            let (lower_bound, _upper_bound) = self.replace_with.size_hint();
            if lower_bound > 0 {
                self.drain.move_tail(lower_bound);
                if !self.drain.fill(&mut self.replace_with) {
                    return;
                }
            }

            // Collect any remaining elements.
            // This is a zero-length vector which does not allocate if `lower_bound` was exact.
            let mut collected =
                self.replace_with.by_ref().collect::<Vec<I::Item>>().into_iter();
            // Now we have an exact count.
            if collected.len() > 0 {
                self.drain.move_tail(collected.len());
                let filled = self.drain.fill(&mut collected);
                debug_assert!(filled);
                debug_assert_eq!(collected.len(), 0);
            }
        }
        // Let `Drain::drop` move the tail back if necessary and restore `vec.len`.
    }
}

/// Private helper methods for `Splice::drop`
impl<T: Clone> Drain<'_, T> {
    /// The range from `self.vec.len` to `self.tail_start` contains elements
    /// that have been moved out.
    /// Fill that range as much as possible with new elements from the `replace_with` iterator.
    /// Returns `true` if we filled the entire range. (`replace_with.next()` didn’t return `None`.)
    unsafe fn fill<I: Iterator<Item = T>>(&mut self, replace_with: &mut I) -> bool {
        let vec = unsafe { self.vec.as_mut() };
        let range_start = vec.len();
        let range_end = self.tail_start;
        let range_slice = unsafe {
            slice::from_raw_parts_mut(
                vec.as_mut_ptr().add(range_start),
                range_end - range_start,
            )
        };

        for place in range_slice {
            let Some(new_item) = replace_with.next() else {
                return false;
            };
            unsafe { ptr::write(place, new_item) };
            vec.set_len(vec.len() + 1);
        }
        true
    }

    /// Makes room for inserting more elements before the tail.
    unsafe fn move_tail(&mut self, additional: usize) {
        let vec = unsafe { self.vec.as_mut() };
        let len = self.tail_start + self.tail_len;
        let capacity = vec.capacity();
        if additional > capacity - len {
            let target = EcoVec::<T>::amortized_cap(len, additional, capacity);
            vec.grow(target);
        }

        let new_tail_start = self.tail_start + additional;
        unsafe {
            let src = vec.as_ptr().add(self.tail_start);
            let dst = vec.as_mut_ptr().add(new_tail_start);
            ptr::copy(src, dst, self.tail_len);
        }
        self.tail_start = new_tail_start;
    }
}
