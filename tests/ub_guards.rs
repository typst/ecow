use ecow::{eco_vec, EcoVec};

// Guarding against something like:
// https://github.com/servo/rust-smallvec/issues/96 aka RUSTSEC-2018-0003
// If length isn't updated defensively then a panic when iterating could
// double-free a value.
#[test]
#[should_panic(expected = "Panic on next")]
fn panicky_iterator_unwinds_correctly() {
    struct PanicIter;

    impl Iterator for PanicIter {
        type Item = u32;

        fn size_hint(&self) -> (usize, Option<usize>) {
            (1, None)
        }

        fn next(&mut self) -> Option<Self::Item> {
            panic!("Panic on next");
        }
    }

    let mut v = eco_vec![1, 2, 3];
    v.extend(PanicIter);
}

// Guarding against something like:
// https://github.com/servo/rust-smallvec/issues/252 aka RUSTSEC-2021-0003
// size_hint should only be treated as a hint, nothing more.
#[test]
fn small_size_hint_is_fine() {
    let mut v = EcoVec::new();
    v.push(123);

    let iter = (0u8..=255).filter(|n| n % 2 == 0);
    assert_eq!(iter.size_hint().0, 0);

    v.extend(iter);

    assert_eq!(
        v,
        core::iter::once(123)
            .chain((0u8..=255).filter(|n| n % 2 == 0))
            .collect::<Vec<_>>()
    );
}

// Guarding against something like:
// https://github.com/Alexhuszagh/rust-stackvector/issues/2 aka RUSTSEC-2021-0048
// size_hint should only be treated as a hint, nothing more.
#[test]
fn wacky_size_hint_is_fine() {
    struct IncorrectIterator(core::iter::Take<core::iter::Repeat<u8>>);

    impl IncorrectIterator {
        pub fn new() -> Self {
            IncorrectIterator(core::iter::repeat(1).take(20))
        }
    }

    impl Iterator for IncorrectIterator {
        type Item = u8;

        fn next(&mut self) -> Option<Self::Item> {
            self.0.next()
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (20, Some(0))
        }
    }

    let mut v = EcoVec::new();
    v.extend(IncorrectIterator::new());

    assert_eq!(v, IncorrectIterator::new().collect::<Vec<_>>())
}
