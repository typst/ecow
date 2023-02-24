// Test with `cargo +nightly miri test` to check sanity!

use alloc::boxed::Box;
use alloc::string::ToString;
use alloc::vec::Vec;
use core::mem;
use core::sync::atomic::{AtomicUsize, Ordering::*};

use super::*;
use crate::dynamic::LIMIT;

const ALPH: &str = "abcdefghijklmnopqrstuvwxyz";

fn v<T>(value: T) -> Box<T> {
    Box::new(value)
}

#[test]
fn test_mem_size() {
    let word = mem::size_of::<usize>();
    assert_eq!(mem::size_of::<EcoVec<u8>>(), 2 * word);
    assert_eq!(mem::size_of::<Option<EcoVec<u8>>>(), 2 * word);

    if cfg!(target_endian = "little") {
        if cfg!(target_pointer_width = "32") {
            // Inline length still should be reasonable on 32-bit systems
            assert_eq!(mem::size_of::<EcoString>(), 4 * word);
            // No niche :(
            assert_eq!(mem::size_of::<Option<EcoString>>(), 5 * word);
        } else if cfg!(target_pointer_width = "64") {
            assert_eq!(mem::size_of::<EcoString>(), 2 * word);
            // No niche :(
            assert_eq!(mem::size_of::<Option<EcoString>>(), 3 * word);
        }
    }
}

#[test]
fn test_vec_macro() {
    assert_eq!(eco_vec![Box::new(1); 3], alloc::vec![v(1); 3]);
}

#[test]
fn test_vec_with_capacity() {
    let mut vec = EcoVec::with_capacity(3);
    assert_eq!(vec.capacity(), 3);
    let ptr = vec.as_ptr();
    vec.push(1);
    vec.push(2);
    vec.push(3);
    assert_eq!(ptr, vec.as_ptr());
    vec.push(4);
    assert_eq!(vec, [1, 2, 3, 4]);
}

#[test]
#[should_panic(expected = "capacity overflow")]
fn test_vec_with_capacity_fail() {
    EcoVec::<u8>::with_capacity(usize::MAX);
}

#[test]
fn test_vec_empty() {
    let mut first = EcoVec::with_capacity(3);
    assert!(first.is_empty());
    assert_eq!(first.len(), 0);
    first.push("hi".to_string());
    assert!(!first.is_empty());
    assert_eq!(first.len(), 1);
    let second = first.clone();
    first.clear();
    assert!(first.is_empty());
    assert_eq!(second.len(), 1);
    assert_eq!(second, ["hi".to_string()]);
}

#[test]
fn test_vec_make_mut() {
    let mut first = eco_vec![4, -3, 11, 6, 10];
    let ptr = first.as_ptr();
    first.make_mut()[1] -= 1;
    assert_eq!(ptr, first.as_ptr());
    let second = first.clone();
    first.make_mut().sort();
    assert_eq!(first, [-4, 4, 6, 10, 11]);
    assert_eq!(second, [4, -4, 11, 6, 10]);
}

#[test]
fn test_vec_push() {
    let mut first = EcoVec::new();
    first.push(1);
    first.push(2);
    first.push(3);
    assert_eq!(first.len(), 3);
    let mut second = first.clone();
    let third = second.clone();
    let _ = third.clone();
    second.push(4);
    assert_eq!(second.len(), 4);
    assert_eq!(first, [1, 2, 3]);
    assert_eq!(second, [1, 2, 3, 4]);
    assert_eq!(third, [1, 2, 3]);
    assert_ne!(first.as_ptr(), second.as_ptr());
    assert_eq!(first.as_ptr(), third.as_ptr());
}

#[test]
fn test_vec_pop() {
    let mut first = EcoVec::new();
    assert_eq!(first.pop(), None);
    first.push(v("a"));
    let ptr = first.as_ptr();
    assert_eq!(first.pop(), Some(v("a")));
    first.push(v("b"));
    assert_eq!(ptr, first.as_ptr());
    let second = first.clone();
    assert_eq!(first[0], v("b"));
    assert_eq!(ptr, first.as_ptr());
    assert_eq!(first.pop(), Some(v("b")));
    assert_eq!(first, []);
    assert_eq!(second, [v("b")]);
}

#[test]
fn test_vec_insert() {
    let mut first = EcoVec::new();
    first.insert(0, "okay");
    let ptr = first.as_ptr();
    first.insert(0, "reverse");
    let mut second = first.clone();
    first.insert(2, "a");
    first.insert(1, "b");
    second.insert(2, "last");
    assert_eq!(first, ["reverse", "b", "okay", "a"]);
    assert_eq!(second, ["reverse", "okay", "last"]);
    assert_ne!(ptr, first.as_ptr());
    assert_eq!(ptr, second.as_ptr());
}

#[test]
#[should_panic(expected = "index is out bounds (index: 4, len: 3)")]
fn test_vec_insert_fail() {
    EcoVec::from([1, 2, 3]).insert(4, 0);
}

#[test]
fn test_vec_remove() {
    let mut first = EcoVec::with_capacity(4);
    let ptr = first.as_ptr();
    first.extend_from_slice(&[v(2), v(4), v(1)]);
    let second = first.clone();
    assert_eq!(first.remove(1), v(4));
    assert_eq!(first, [v(2), v(1)]);
    assert_eq!(second, [v(2), v(4), v(1)]);
    assert_ne!(ptr, first.as_ptr());
    assert_eq!(ptr, second.as_ptr());
}

#[test]
fn test_vec_truncate() {
    let mut vec = eco_vec!["ok"; 10];
    vec.truncate(13);
    vec.truncate(3);
    assert_eq!(vec, ["ok"; 3])
}

#[test]
fn test_vec_extend() {
    let mut vec = EcoVec::new();
    vec.extend_from_slice(&[]);
    vec.extend_from_byte_slice(&[2, 3, 4]);
    assert_eq!(vec, [2, 3, 4]);
}

#[test]
fn test_vec_into_iter() {
    let first = eco_vec![v(2), v(4), v(5)];
    let mut second = first.clone();
    assert_eq!(first.clone().into_iter().count(), 3);
    assert_eq!(second.clone().into_iter().rev().collect::<Vec<_>>(), [v(5), v(4), v(2)]);
    second.clear();
    assert_eq!(second.into_iter().collect::<Vec<_>>(), []);
    assert_eq!(first.clone().into_iter().collect::<Vec<_>>(), [v(2), v(4), v(5)]);
    let mut iter = first.into_iter();
    assert_eq!(iter.len(), 3);
    assert_eq!(iter.next(), Some(v(2)));
    assert_eq!(iter.next_back(), Some(v(5)));
    assert_eq!(iter.as_slice(), [v(4)]);
    drop(iter);
}

#[test]
fn test_vec_zst() {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    #[derive(Clone)]
    struct Potato;
    impl Drop for Potato {
        fn drop(&mut self) {
            COUNTER.fetch_add(1, SeqCst);
        }
    }

    let mut vec = EcoVec::new();
    for _ in 0..1000 {
        vec.push(Potato);
    }
    assert_eq!(vec.len(), 1000);
    drop(vec);

    assert_eq!(COUNTER.load(SeqCst), 1000);
}

#[test]
fn test_vec_huge_alignment() {
    #[derive(Debug, PartialEq, Clone)]
    #[repr(align(128))]
    struct B(&'static str);
    let mut vec: EcoVec<B> =
        "hello, world! what's going on?".split_whitespace().map(B).collect();

    assert_eq!(vec.len(), 5);
    assert_eq!(vec.capacity(), 8);
    assert_eq!(vec, [B("hello,"), B("world!"), B("what's"), B("going"), B("on?")]);
    assert_eq!(vec.pop(), Some(B("on?")));
    assert_eq!(vec.len(), 4);
    assert_eq!(vec.last(), Some(&B("going")));
    assert_eq!(vec.remove(1), B("world!"));
    assert_eq!(vec.len(), 3);
    assert_eq!(vec, [B("hello,"), B("what's"), B("going")]);
    assert_eq!(vec[1], B("what's"));
    vec.push(B("where?"));
    vec.insert(1, B("wonder!"));
    assert_eq!(vec, [B("hello,"), B("wonder!"), B("what's"), B("going"), B("where?")]);
    vec.retain(|b| b.0.starts_with('w'));
    assert_eq!(vec, [B("wonder!"), B("what's"), B("where?")]);
    vec.truncate(1);
    assert_eq!(vec.last(), vec.first());
}

#[test]
#[should_panic(expected = "dropped the hot potato!")]
fn test_vec_drop_panic() {
    #[derive(Clone)]
    struct Potato;
    impl Drop for Potato {
        fn drop(&mut self) {
            panic!("dropped the hot potato!");
        }
    }

    eco_vec![Potato];
}

#[test]
#[should_panic(expected = "dropped the hot potato!")]
fn test_vec_clear_drop_panic() {
    #[derive(Clone)]
    struct Potato;
    impl Drop for Potato {
        fn drop(&mut self) {
            panic!("dropped the hot potato!");
        }
    }

    let mut vec = eco_vec![Potato];
    vec.clear();
}

#[test]
fn test_str_new() {
    // Test inline strings.
    assert_eq!(EcoString::new(), "");
    assert_eq!(EcoString::from('a'), "a");
    assert_eq!(EcoString::from('😀'), "😀");
    assert_eq!(EcoString::from("abc"), "abc");

    // Test around the inline limit.
    assert_eq!(EcoString::from(&ALPH[..LIMIT - 1]), ALPH[..LIMIT - 1]);
    assert_eq!(EcoString::from(&ALPH[..LIMIT]), ALPH[..LIMIT]);
    assert_eq!(EcoString::from(&ALPH[..LIMIT + 1]), ALPH[..LIMIT + 1]);

    // Test heap string.
    assert_eq!(EcoString::from(ALPH), ALPH);
}

#[test]
fn test_str_push() {
    let mut v = EcoString::new();
    v.push('a');
    v.push('b');
    v.push_str("cd😀");
    assert_eq!(v, "abcd😀");
    assert_eq!(v.len(), 8);

    // Test fully filling the inline storage.
    v.push_str("efghijk");
    assert_eq!(v.len(), 15);

    // Test spilling with `push`.
    let mut a = v.clone();
    assert_eq!(a, "abcd😀efghijk");
    a.push('l');
    assert_eq!(a, "abcd😀efghijkl");
    assert_eq!(a.len(), 16);

    // Test spilling with `push_str`.
    let mut b = v.clone();
    b.push_str("lmn");
    assert_eq!(b, "abcd😀efghijklmn");
    assert_eq!(b.len(), 18);

    // v should be unchanged.
    assert_eq!(v.len(), 15);
}

#[test]
fn test_str_pop() {
    // Test with inline string.
    let mut v = EcoString::from("Hello World!");
    assert_eq!(v.pop(), Some('!'));
    assert_eq!(v, "Hello World");

    // Remove one-by-one.
    for _ in 0..10 {
        v.pop();
    }

    assert_eq!(v, "H");
    assert_eq!(v.pop(), Some('H'));
    assert_eq!(v, "");
    assert!(v.is_empty());

    // Test with large string.
    let mut v = EcoString::from(ALPH);
    assert_eq!(v.pop(), Some('z'));
    assert_eq!(v.len(), 25);
}

#[test]
fn test_str_index() {
    // Test that we can use the index syntax.
    let v = EcoString::from("abc");
    assert_eq!(&v[..2], "ab");
}

#[test]
fn test_str_case() {
    assert_eq!(EcoString::new().to_uppercase(), "");
    assert_eq!(EcoString::from("abc").to_uppercase(), "ABC");
    assert_eq!(EcoString::from("AΣ").to_lowercase(), "aς");
    assert_eq!(
        EcoString::from("a").repeat(100).to_uppercase(),
        EcoString::from("A").repeat(100)
    );
    assert_eq!(
        EcoString::from("Ö").repeat(20).to_lowercase(),
        EcoString::from("ö").repeat(20)
    );
}

#[test]
fn test_str_repeat() {
    // Test with empty string.
    assert_eq!(EcoString::new().repeat(0), "");
    assert_eq!(EcoString::new().repeat(100), "");

    // Test non-spilling and spilling case.
    let v = EcoString::from("abc");
    assert_eq!(v.repeat(0), "");
    assert_eq!(v.repeat(3), "abcabcabc");
    assert_eq!(v.repeat(5), "abcabcabcabcabc");
}

#[test]
fn test_str_inline_okay() {
    assert_eq!(EcoString::inline("hello"), "hello");
}

#[test]
#[should_panic(expected = "exceeded inline capacity")]
fn test_str_inline_capacity_exceeded() {
    EcoString::inline("this is a pretty long string");
}
