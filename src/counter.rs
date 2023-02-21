use core::{
    cell::Cell,
    sync::atomic::{self, AtomicUsize, Ordering::*},
};

/// A counter that can be incremented and decremented
pub trait Counter {
    /// Returns a counter with value one
    fn one() -> Self;

    /// Returns true if this counter is one, otherwise false
    fn is_one(&self) -> bool;

    /// Increments the counter
    /// Returns true if counter has overflown, otherwise false
    fn incr(&self) -> bool;

    /// Decrements the counter
    /// Returns true if counter has reached zero, otherwise false
    fn decr(&self) -> bool;
}

impl Counter for Cell<usize> {
    fn one() -> Self {
        Cell::new(1)
    }

    fn is_one(&self) -> bool {
        self.get() == 1
    }

    fn incr(&self) -> bool {
        let prev = self.get();
        self.set(prev + 1);
        prev > isize::MAX as usize
    }

    fn decr(&self) -> bool {
        let prev = self.get();
        self.set(prev - 1);
        prev == 1
    }
}

impl Counter for AtomicUsize {
    fn one() -> Self {
        AtomicUsize::new(1)
    }

    fn is_one(&self) -> bool {
        // See Arc's is_unique() method.
        self.load(Acquire) == 1
    }

    fn incr(&self) -> bool {
        // See Arc's clone impl for details about memory ordering.
        let prev = self.fetch_add(1, Relaxed);
        prev > isize::MAX as usize
    }

    fn decr(&self) -> bool {
        // See Arc's drop impl for details about memory ordering.
        if self.fetch_sub(1, Release) == 1 {
            // See Arc's drop impl for details.
            atomic::fence(Acquire);
            true
        } else {
            false
        }
    }
}
