/*!
Compact, clone-on-write vector and string.

## Types
- An [`EcoVec`] is a reference-counted clone-on-write vector with the same
  memory layout as  a slice `&[T]`. It takes up two words of space (= 2 usize).
  Within its allocation it stores a reference count and its capacity.

- An [`EcoString`] is a reference-counted string with inline storage. It takes
  up 24 bytes of space. It has 14 bytes of inline storage and starting from 15
  bytes it becomes an [`EcoVec<u8>`].

## Example
```
// This is stored inline.
let small = ecow::EcoString::from("Welcome");

// This spills to the heap, but only once: `big` and `third` share the
// same underlying allocation. Vectors and spilled strings are only
// really cloned upon mutation.
let big = small + " to earth! 🌱";
let mut third = big.clone();

// This allocates again to mutate `third` without affecting `big`.
assert_eq!(third.pop(), Some('🌱'));
assert_eq!(third, "Welcome to earth! ");
```

## Why should I use this instead of ...

| Type                                        | Details |
|:--------------------------------------------|:--------|
| [`Vec<T>`] / [`String`]                     | Normal vectors are a great general purpose data structure. But they have a quite big footprint (3 machine words) and are expensive to clone. The [`EcoVec`] has a bit of overhead for mutation, but is cheap to clone and only takes two words. |
| [`Arc<Vec<T>>`][arc] / [`Arc<String>`][arc] | These require two allocations instead of one and are less convenient to mutate. |
| [`Arc<[T]>`][arc] / [`Arc<str>`][arc]       | While these require only one allocation, they aren't mutable. |
| Small vector                                | Different trade-off. Great when there are few, small `T`s, but expensive to clone when spilled to the heap. |
| Other small strings                         | The [`EcoString`] combines different small string qualities into a very practical package: It has inline storage, a smaller footprint than a normal [`String`], is efficient to clone even when spilled, and at the same time mutable. |

[arc]: std::sync::Arc
*/

#![no_std]
#![deny(missing_docs)]

extern crate alloc;

mod string;
mod vec;

pub use string::*;
pub use vec::*;

#[cfg(test)]
mod tests;
