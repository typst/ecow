/*!
Compact, clone-on-write vector and string.

- The [`EcoVec`] is a reference-counted thin vector. It takes up one word of
  space (= 1 usize). Within its allocation it stores a reference count, its
  length, and its capacity. The empty vector does not allocate and the
  whole vector is null-pointer optimized.

- The [`EcoString`] takes up 16 bytes of space. It has 14 bytes of inline
  storage and starting from 15 bytes it becomes an `EcoVec<u8>`.
*/

mod string;
mod vec;

pub use string::*;
pub use vec::*;
