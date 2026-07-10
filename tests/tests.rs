// Test with `cargo +nightly miri test` to check sanity!

#![allow(clippy::redundant_clone)]
#![allow(clippy::disallowed_names)]

use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt::Write;
use std::mem;
use std::sync::atomic::{AtomicUsize, Ordering::*};

use ecow::string::ToEcoString;
use ecow::{eco_format, eco_vec, EcoString, EcoVec};

const ALPH: &str = "abcdefghijklmnopqrstuvwxyz";
const LIMIT: usize = EcoString::INLINE_LIMIT;

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
    assert_eq!(eco_vec![Box::new(1); 3], vec![v(1); 3]);
}

#[test]
fn test_vec_construction() {
    assert_eq!(EcoVec::<()>::default(), &[]);
    assert_eq!(EcoVec::from(vec![(); 100]), vec![(); 100]);
}

#[test]
fn test_from_vec_rc() {
    use std::rc::Rc;

    let x = Rc::new(());
    let v = vec![x.clone()];
    assert_eq!(Rc::strong_count(&x), 2);

    let vec = EcoVec::from(v);
    assert_eq!(Rc::strong_count(&x), 2, "Rc count should not change");
    assert_eq!(vec.len(), 1);
    assert!(Rc::ptr_eq(&x, &vec[0]));

    std::mem::drop(vec);
    assert_eq!(Rc::strong_count(&x), 1);
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
#[should_panic(expected = "index is out bounds (index: 4, len: 3)")]
fn test_vec_remove_fail() {
    EcoVec::from([1, 2, 3]).remove(4);
}

#[test]
fn test_vec_truncate() {
    let mut vec = eco_vec!["ok"; 10];
    vec.truncate(13);
    vec.truncate(3);
    assert_eq!(vec, ["ok"; 3]);

    let mut cloned = vec.clone();
    cloned.truncate(2);
    assert_eq!(cloned, ["ok"; 2]);
}

#[test]
fn test_vec_drain() {
    let mut vec = EcoVec::from_elem(v("a"), 10);
    vec.drain(3..6);
    assert_eq!(vec.len(), 7);

    // Manually pull an item, before dropping the drain.
    let mut drain = vec.drain(5..);
    drain.next();
    drop(drain);
    assert_eq!(vec.len(), 5);

    let mut cloned = vec.clone();
    cloned.drain(..2);
    assert_eq!(cloned.len(), 3);

    let drained = cloned.drain(..).collect::<Vec<_>>();
    assert_eq!(drained.len(), 3);
    assert_eq!(cloned, []);
}

#[test]
fn test_vec_splice() {
    let mut vec = eco_vec!["a"; 6];
    // Inserted iterator is smaller.
    vec.splice(2..4, ["b"; 1]);
    assert_eq!(vec, ["a", "a", "b", "a", "a"]);

    // Inserted iterator is larger.
    let mut cloned = vec.clone();
    cloned.splice(3..4, ["c"; 3]);
    assert_eq!(cloned, ["a", "a", "b", "c", "c", "c", "a"]);

    // Inserted iterator is the same size.
    cloned.splice(2..6, ["d"; 4]);
    assert_eq!(cloned, ["a", "a", "d", "d", "d", "d", "a"]);

    // Insert an interator that doesn't have exact size hints.
    cloned.splice(1..6, ["e"; 3].into_iter().filter(|_| true));
    assert_eq!(cloned, ["a", "e", "e", "e", "a"]);
}

#[test]
fn test_vec_extend() {
    let mut vec = EcoVec::new();
    vec.extend_from_slice(&[]);
    vec.extend_from_slice(&[2, 3, 4]);
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

    let empty: EcoVec<B> = EcoVec::new();
    assert_eq!(empty, &[]);
}

#[test]
#[should_panic(expected = "dropped the hot potato!")]
#[allow(unused_must_use)]
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
fn test_array_from_vec() {
    let array = [String::from("foo"), String::from("bar")];
    let a = EcoVec::from(array.clone());
    let b = a.clone();
    let c: [String; 2] = a.try_into().unwrap();
    assert_eq!(b, c);
    let d = b.clone();
    assert_eq!(c, array);
    assert_eq!(d, array);
    drop(b);
    assert_eq!(c, array);
    drop(d);
    assert_eq!(c, array);

    assert_eq!(<[String; 0]>::try_from(EcoVec::new()).unwrap(), <[String; 0]>::default());
}

#[test]
fn test_str_macro() {
    assert_eq!(
        eco_format!("Hello, {}! The secret number is {}.", "world".to_owned(), 42),
        "Hello, world! The secret number is 42."
    );
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
fn test_str_insert() {
    let mut v = EcoString::new();
    v.insert(0, 'a');
    v.insert(1, '😀');
    v.insert_str(1, "bcd");
    assert_eq!(v, "abcd😀");
    assert_eq!(v.len(), 8);

    // Test fully filling the inline storage.
    v.insert_str(8, "efghijk");
    assert_eq!(v.len(), 15);

    // Test spilling with `insert`.
    let mut a = v.clone();
    assert_eq!(a, "abcd😀efghijk");
    a.insert(8, '_');
    assert_eq!(a, "abcd😀_efghijk");
    assert_eq!(a.len(), 16);

    // Test spilling with `insert_str`.
    let mut b = v.clone();
    b.insert_str(2, "._.");
    assert_eq!(b, "ab._.cd😀efghijk");
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
fn test_str_remove() {
    // Test with inline string.
    let mut v = EcoString::from("Hello World!");
    assert_eq!(v.remove(0), 'H');
    assert_eq!(v, "ello World!");

    // Remove one-by-one.
    for i in (4..10).rev() {
        v.remove(i);
    }
    assert_eq!(v, "ello!");

    for _ in 0..5 {
        v.remove(0);
    }
    assert!(v.is_empty());

    // Test with large string.
    let mut v = EcoString::from(ALPH);
    assert_eq!(v.remove(21), 'v');
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

#[test]
fn test_str_clear() {
    let mut inline_clear = EcoString::from("foo");
    inline_clear.clear();
    assert_eq!(inline_clear, "");

    let mut spilled_clear: EcoString = std::iter::repeat('a').take(100).collect();
    let cloned = spilled_clear.clone();
    spilled_clear.clear();
    assert_eq!(spilled_clear, "");
    assert_eq!(cloned.len(), 100);
}

#[test]
fn test_str_construction() {
    let from_cow = EcoString::from(Cow::Borrowed("foo"));
    let from_char_iter: EcoString = "foo".chars().collect();
    let from_eco_string_iter: EcoString =
        [EcoString::from("f"), EcoString::from("oo")].into_iter().collect();

    assert_eq!(from_cow, from_char_iter);
    assert_eq!(from_char_iter, from_eco_string_iter);
    assert_eq!(from_eco_string_iter, "foo");

    let str_from_eco_string_ref = String::from(&from_cow);
    let str_from_eco_string = String::from(from_cow);

    assert_eq!(str_from_eco_string, str_from_eco_string_ref);
    assert_eq!(str_from_eco_string_ref, "foo");

    let from_string_iter: EcoString = ["foo", " ", "bar"].into_iter().collect();

    assert_eq!(from_string_iter, "foo bar");
}

#[test]
fn test_str_extend() {
    let mut s = EcoString::from("Hello, ");
    s.extend("world!".chars());

    s.extend([" How ", "are ", "you", "?"]);

    assert_eq!(s, "Hello, world! How are you?");
}

#[test]
fn test_str_add() {
    let hello = EcoString::from("Hello, ");
    let world = EcoString::from("world!");

    let add = hello.clone() + world.clone();
    let mut add_assign = hello.clone();
    add_assign += world;

    assert_eq!(add, add_assign);
    assert_eq!(add, "Hello, world!");

    let add_str = hello.clone() + "world!";
    let mut add_assign_str = hello.clone();
    add_assign_str += "world!";

    assert_eq!(add_str, add_assign_str);
    assert_eq!(add_str, "Hello, world!");
}

#[test]
fn test_str_complex() {
    let mut foo = EcoString::default();
    foo.write_char('f').unwrap();
    foo.write_str("oo").unwrap();

    let bar = EcoString::from("bar");

    let mut hash_map: HashMap<_, EcoVec<_>> = [
        (foo.clone(), eco_vec![foo.clone(), bar.clone(), foo]),
        (bar.clone(), eco_vec![bar; 1]),
    ]
    .into_iter()
    .collect();

    hash_map.get_mut("foo").unwrap().make_mut().sort();

    assert_eq!(hash_map.get("foo").unwrap(), &["bar".into(), "foo".into(), "foo".into()]);
    assert_eq!(hash_map.get("bar").unwrap(), &["bar".into()]);
}

#[test]
fn test_str_to_eco_string() {
    let num = 123456789;
    assert_eq!(num.to_eco_string(), "123456789");
}

mod map {
    use std::fmt::Debug;

    use ecow::EcoMap;

    #[test]
    fn test_with_capacity() {
        let m = EcoMap::<i32, i32, 8>::with_capacity(4);
        let m2 = EcoMap::<i32, i32, 8>::with_capacity(8);
        let m3 = EcoMap::<i32, i32, 8>::with_capacity(10);

        assert_eq!(m.capacity(), 8);
        assert_eq!(m2.capacity(), 8);
        assert!(m3.capacity() >= 10);
    }

    #[test]
    fn test_insert() {
        let mut m = EcoMap::<_, _, 8>::new();
        assert_eq!(m.len(), 0);
        assert!(m.insert(1, 2).is_none());
        assert_eq!(m.len(), 1);
        assert!(m.insert(2, 4).is_none());
        assert_eq!(m.len(), 2);
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert_eq!(*m.get(&2).unwrap(), 4);

        // Test replacing values
        assert_eq!(m.insert(1, 20), Some(2));
        assert_eq!(*m.get(&1).unwrap(), 20);
    }

    #[test]
    fn test_empty_remove() {
        let mut m: EcoMap<i32, bool, 8> = EcoMap::new();
        assert_eq!(m.remove(&0), None);
    }

    #[test]
    fn test_spill_on_full() {
        // Create a map with an inline capacity of exactly 4
        let mut m = EcoMap::<i32, i32, 4>::new();

        // Fill it perfectly up to capacity
        for i in 0..4 {
            assert!(m.insert(i, i * 10).is_none());
        }
        assert_eq!(m.len(), 4);
        assert_eq!(m.capacity(), 4); // Still inline

        // Trigger the spill by pushing past inline capacity N
        assert!(m.insert(4, 40).is_none());
        assert_eq!(m.len(), 5);
        assert!(m.capacity() >= 6); // Verifies 1.5x or similar heap allocation occurred

        // Ensure all historical data remained perfectly intact post-spill
        for i in 0..=4 {
            assert_eq!(m.get(&i), Some(&(i * 10)));
        }
    }

    #[test]
    fn test_linear_probing_and_backward_shift() {
        // We use a small capacity map to intentionally encourage collisions
        let mut m = EcoMap::<i32, i32, 4>::new();

        // Insert enough elements to create potential collision clusters
        m.insert(1, 10);
        m.insert(2, 20);
        m.insert(3, 30);

        // Remove a middle element to trigger backward-shift logic
        assert_eq!(m.remove(&2), Some(20));
        assert_eq!(m.len(), 2);

        // Crucial invariant check: Linear probing chains must not be broken!
        // If the backward shift failed, lookups for items further down the chain will fail.
        assert_eq!(m.get(&1), Some(&10));
        assert_eq!(m.get(&3), Some(&30));
    }

    #[test]
    fn test_remove_from_full_inline_map() {
        let mut map = EcoMap::<i32, i32, 4>::new();
        for i in 0..4 {
            map.insert(i, i * 10);
        }
        assert_eq!(map.len(), 4);
        assert_eq!(map.capacity(), 4);

        assert_eq!(map.remove(&1), Some(10));
        assert_eq!(map.len(), 3);
        assert_eq!(map.get(&1), None);

        for i in [0, 2, 3] {
            assert_eq!(map.get(&i), Some(&(i * 10)));
        }

        map.insert(4, 40);
        assert_eq!(map.len(), 4);
        for i in [0, 2, 3, 4] {
            assert_eq!(map.get(&i), Some(&(i * 10)));
        }
    }

    #[test]
    fn test_shrink_to() {
        let mut map = EcoMap::<i32, i32, 4>::new();

        // Force it to spill
        for i in 0..10 {
            map.insert(i, i);
        }
        assert!(map.capacity() > 4);

        map.retain(|&k, _| k >= 8);

        // shrink_to with a high min_capacity should keep it spilled
        map.shrink_to(10);
        assert!(map.capacity() > 4, "should still be spilled");
        assert_eq!(map.len(), 2);

        // shrink_to with a low min_capacity should inline it back
        map.shrink_to(0);
        assert_eq!(map.capacity(), 4);
        assert_eq!(map.len(), 2);

        // Check structural integrity of inlined items
        for i in 8..10 {
            assert_eq!(map.get(&i), Some(&i));
        }
    }

    #[test]
    fn test_shrink_to_and_inlining() {
        let mut m = EcoMap::<i32, i32, 4>::new();

        // Force it to spill
        for i in 0..10 {
            m.insert(i, i);
        }
        assert!(m.capacity() > 4);

        // Remove elements until it has 3 elements
        // This leaves 1 empty slot (a gap) when we inline it back to N = 4.
        for i in 3..10 {
            m.remove(&i);
        }
        assert_eq!(m.len(), 3);

        // Call shrink_to_fit / shrink_to to see if it moves back to the stack
        m.shrink_to_fit();

        assert_eq!(m.capacity(), 4); // Verifies it completely inlined back down
        assert_eq!(m.len(), 3);

        // Check structural integrity of inlined items
        for i in 0..3 {
            assert_eq!(m.get(&i), Some(&i));
        }
    }

    #[test]
    fn test_spilled_clone_shrink_safety() {
        let mut map = EcoMap::<_, _>::new();
        // Fill until spilled
        for i in 0..20 {
            map.insert(i, i);
        }

        let cloned = map.clone();

        map.clear();
        map.shrink_to_fit();

        // Verify the first map is now Inline (or smaller)
        assert!(matches!(map, EcoMap::Inline { .. }));

        // Verify the clone is still Spilled and data is intact
        assert!(matches!(cloned, EcoMap::Spilled(_)));
        assert_eq!(cloned.len(), 20);
        assert_eq!(cloned.get(&5), Some(&5));
    }

    #[test]
    fn test_get_mut() {
        let mut m = EcoMap::<&str, i32, 4>::new();
        m.insert("hello", 1);

        if let Some(val) = m.get_mut(&"hello") {
            *val = 42;
        }

        assert_eq!(m.get(&"hello"), Some(&42));
    }

    #[test]
    fn test_ref_extend_and_from_iter() {
        let pairs = [("a".to_owned(), 1), ("b".to_owned(), 2), ("c".to_owned(), 3)];

        let map: EcoMap<String, i32, 4> =
            pairs.iter().map(|(key, value)| (key, value)).collect();
        assert_eq!(map.get("a"), Some(&1));
        assert_eq!(map.get("b"), Some(&2));
        assert_eq!(map.get("c"), Some(&3));

        let mut extended = EcoMap::<String, i32, 4>::new();
        extended.extend(pairs.iter().map(|(key, value)| (key, value)));
        assert_eq!(extended, map);
    }

    #[test]
    fn test_iterator_defaults() {
        let iter: ecow::map::EcoIter<'_, i32, i32, 4> = Default::default();
        assert_eq!(iter.len(), 0);
        assert_eq!(format!("{:?}", iter), "[]");

        let iter_mut: ecow::map::EcoIterMut<'_, i32, i32, 4> = Default::default();
        assert_eq!(iter_mut.len(), 0);
        assert_eq!(format!("{:?}", iter_mut), "[]");

        let keys: ecow::map::Keys<'_, i32, i32, 4> = Default::default();
        assert_eq!(keys.len(), 0);
        assert_eq!(format!("{:?}", keys), "[]");

        let values: ecow::map::Values<'_, i32, i32, 4> = Default::default();
        assert_eq!(values.len(), 0);
        assert_eq!(format!("{:?}", values), "[]");

        let values_mut: ecow::map::ValuesMut<'_, i32, i32, 4> = Default::default();
        assert_eq!(values_mut.len(), 0);
        assert_eq!(format!("{:?}", values_mut), "[]");

        let into_keys: ecow::map::IntoKeys<i32, i32, 4> = Default::default();
        assert_eq!(into_keys.len(), 0);
        assert_eq!(format!("{:?}", into_keys), "[]");

        let into_values: ecow::map::IntoValues<i32, i32, 4> = Default::default();
        assert_eq!(into_values.len(), 0);
        assert_eq!(format!("{:?}", into_values), "[]");
    }

    #[test]
    fn test_iterator_debug() {
        let mut map = EcoMap::<i32, i32, 4>::new();
        map.insert(1, 10);

        assert_eq!(format!("{:?}", map.iter_mut()), "[(1, 10)]");
        assert_eq!(format!("{:?}", map.values_mut()), "[10]");
        assert_eq!(format!("{:?}", map.clone().into_keys()), "[1]");
        assert_eq!(format!("{:?}", map.into_values()), "[10]");
    }

    #[test]
    fn test_keys_values_and_hasher() {
        let mut map = EcoMap::<i32, i32, 4>::new();
        map.insert(1, 10);
        map.insert(2, 20);
        map.insert(3, 30);

        let mut keys: Vec<i32> = map.keys().copied().collect();
        keys.sort();
        assert_eq!(keys, vec![1, 2, 3]);

        let mut values: Vec<i32> = map.values().copied().collect();
        values.sort();
        assert_eq!(values, vec![10, 20, 30]);

        for value in map.values_mut() {
            *value += 1;
        }
        let mut values: Vec<i32> = map.values().copied().collect();
        values.sort();
        assert_eq!(values, vec![11, 21, 31]);

        let _ = map.hasher();
    }

    #[test]
    fn test_into_keys_and_into_values() {
        let mut map = EcoMap::<i32, i32, 4>::new();
        for i in 0..10 {
            map.insert(i, i * 10);
        }

        let mut keys: Vec<i32> = map.clone().into_keys().collect();
        keys.sort();
        assert_eq!(keys, (0..10).collect::<Vec<_>>());

        let mut values: Vec<i32> = map.into_values().collect();
        values.sort();
        assert_eq!(values, (0..10).map(|i| i * 10).collect::<Vec<_>>());
    }

    #[test]
    fn test_non_clone_from_iter_and_from_array() {
        #[derive(Debug, Hash, PartialEq, Eq)]
        struct Key(i32);

        #[derive(Debug, PartialEq, Eq)]
        struct Value(i32);

        let map: EcoMap<Key, Value, 4> =
            [(Key(1), Value(10)), (Key(2), Value(20)), (Key(3), Value(30))]
                .into_iter()
                .collect();

        assert_eq!(map.get(&Key(1)), Some(&Value(10)));
        assert_eq!(map.get(&Key(2)), Some(&Value(20)));
        assert_eq!(map.get(&Key(3)), Some(&Value(30)));

        let map = EcoMap::<_, _, 4>::from([(Key(4), Value(40)), (Key(5), Value(50))]);
        assert_eq!(map.get(&Key(4)), Some(&Value(40)));
        assert_eq!(map.get(&Key(5)), Some(&Value(50)));
    }

    #[test]
    fn test_eq_trait() {
        fn assert_eq_impl<T: Eq>() {}
        assert_eq_impl::<EcoMap<i32, i32, 4>>();
    }

    #[test]
    fn test_borrowed_lookup() {
        // Inline lookups with borrowed `str` keys into `String` keys.
        let mut map = EcoMap::<String, i32, 4>::new();
        map.insert("alpha".to_owned(), 1);
        map.insert("beta".to_owned(), 2);

        assert_eq!(map.get("alpha"), Some(&1));
        assert!(map.contains_key("beta"));
        assert_eq!(map["alpha"], 1);

        if let Some(value) = map.get_mut("beta") {
            *value = 20;
        }
        assert_eq!(map.get("beta"), Some(&20));

        let (stored_key, stored_value) = map.get_key_value("alpha").unwrap();
        assert_eq!(stored_key, "alpha");
        assert_eq!(stored_value, &1);

        assert_eq!(map.remove("alpha"), Some(1));
        assert!(!map.contains_key("alpha"));

        // Spilled lookups should behave the same way.
        for i in 0..10 {
            map.insert(format!("key-{i}"), i);
        }
        assert!(map.capacity() > 4);
        assert_eq!(map.get("key-7"), Some(&7));
        assert_eq!(map.remove_entry("key-7"), Some(("key-7".to_owned(), 7)));
        assert_eq!(map.get("key-7"), None);
    }

    #[test]
    fn test_entry_api() {
        let mut map = EcoMap::<String, i32, 4>::new();

        *map.entry("apple".to_owned()).or_insert(1) += 1;
        assert_eq!(map.get("apple"), Some(&2));

        map.entry("apple".to_owned())
            .and_modify(|value| *value *= 10)
            .or_insert(0);
        assert_eq!(map.get("apple"), Some(&20));

        let mut called = false;
        map.entry("apple".to_owned()).or_insert_with(|| {
            called = true;
            99
        });
        assert!(!called);
        assert_eq!(map.get("apple"), Some(&20));

        let value = map
            .entry("banana".to_owned())
            .or_insert_with_key(|key| key.len() as i32);
        assert_eq!(*value, 6);
        assert_eq!(map.get("banana"), Some(&6));

        map.entry("counts".to_owned()).or_default();
        assert_eq!(map.get("counts"), Some(&0));

        {
            let occupied = map.entry("fig".to_owned()).insert_entry(70);
            assert_eq!(occupied.key(), "fig");
            assert_eq!(occupied.get(), &70);
        }
        assert_eq!(map.get("fig"), Some(&70));

        {
            let occupied = map.entry("fig".to_owned()).insert_entry(80);
            assert_eq!(occupied.key(), "fig");
            assert_eq!(occupied.get(), &80);
        }
        assert_eq!(map.get("fig"), Some(&80));

        if let ecow::map::Entry::Vacant(vacant) = map.entry("grape".to_owned()) {
            let mut occupied = vacant.insert_entry(90);
            assert_eq!(occupied.key(), "grape");
            assert_eq!(occupied.get(), &90);
            assert_eq!(occupied.insert(91), 90);
        } else {
            panic!("expected vacant entry");
        }
        assert_eq!(map.get("grape"), Some(&91));

        if let ecow::map::Entry::Occupied(mut occupied) = map.entry("apple".to_owned()) {
            assert_eq!(occupied.key(), "apple");
            assert_eq!(occupied.get(), &20);
            assert_eq!(occupied.insert(30), 20);
            assert_eq!(occupied.get_mut(), &mut 30);
        } else {
            panic!("expected occupied entry");
        }
        assert_eq!(map.get("apple"), Some(&30));

        if let ecow::map::Entry::Vacant(vacant) = map.entry("durian".to_owned()) {
            assert_eq!(vacant.key(), "durian");
            let value = vacant.insert(60);
            *value += 1;
        } else {
            panic!("expected vacant entry");
        }
        assert_eq!(map.get("durian"), Some(&61));

        if let ecow::map::Entry::Vacant(vacant) = map.entry("elderberry".to_owned()) {
            assert_eq!(vacant.into_key(), "elderberry".to_owned());
        } else {
            panic!("expected vacant entry");
        }
        assert!(!map.contains_key("elderberry"));

        if let ecow::map::Entry::Occupied(occupied) = map.entry("banana".to_owned()) {
            assert_eq!(occupied.remove_entry(), ("banana".to_owned(), 6));
        } else {
            panic!("expected occupied entry");
        }
        assert!(!map.contains_key("banana"));
    }

    #[test]
    fn test_entry_api_spilled() {
        let mut map = EcoMap::<String, i32, 4>::new();
        for i in 0..10 {
            map.insert(format!("key-{i}"), i);
        }
        assert!(map.capacity() > 4);

        map.entry("key-5".to_owned())
            .and_modify(|value| *value += 100)
            .or_insert(0);
        assert_eq!(map.get("key-5"), Some(&105));

        assert_eq!(*map.entry("new".to_owned()).or_insert(42), 42);
        assert_eq!(map.get("new"), Some(&42));

        {
            let occupied = map.entry("new".to_owned()).insert_entry(43);
            assert_eq!(occupied.key(), "new");
            assert_eq!(occupied.get(), &43);
        }
        assert_eq!(map.get("new"), Some(&43));

        if let ecow::map::Entry::Vacant(vacant) = map.entry("fresh".to_owned()) {
            let occupied = vacant.insert_entry(77);
            assert_eq!(occupied.key(), "fresh");
            assert_eq!(occupied.get(), &77);
        } else {
            panic!("expected vacant entry");
        }
        assert_eq!(map.get("fresh"), Some(&77));

        if let ecow::map::Entry::Occupied(occupied) = map.entry("key-2".to_owned()) {
            assert_eq!(occupied.remove(), 2);
        } else {
            panic!("expected occupied entry");
        }
        assert_eq!(map.get("key-2"), None);
    }

    #[test]
    fn test_clone_and_drop() {
        let mut m = EcoMap::<String, Vec<i32>, 4>::new();
        m.insert("inline_key".to_owned(), vec![1, 2, 3]);

        // Verify cloning deep copies items
        let mut cloned = m.clone();
        assert_eq!(cloned.get(&"inline_key".to_owned()), Some(&vec![1, 2, 3]));

        // Modify clone to ensure isolation
        cloned.insert("inline_key".to_owned(), vec![4, 5]);
        assert_ne!(m.get(&"inline_key".to_owned()), cloned.get(&"inline_key".to_owned()));

        // Drop tests will run implicitly here
    }

    #[test]
    fn test_iteration() {
        let mut m = EcoMap::<i32, i32, 4>::new();
        m.insert(10, 100);
        m.insert(20, 200);

        let mut pairs: Vec<(&i32, &i32)> = m.iter().collect();
        pairs.sort_by_key(|&(&k, _)| k);

        assert_eq!(pairs, vec![(&10, &100), (&20, &200)]);
    }

    #[test]
    fn test_iteration_mut() {
        // Inline
        let mut m = EcoMap::<&str, i32, 4>::new();
        m.insert("a", 1);
        m.insert("b", 2);
        m.insert("c", 3);

        // Mutate values inline
        for (key, val) in m.iter_mut() {
            if *key == "b" {
                *val += 10;
            } else {
                *val *= 2;
            }
        }

        // Verify mutations stuck and order doesn't matter
        assert_eq!(m.get(&"a"), Some(&2));
        assert_eq!(m.get(&"b"), Some(&12));
        assert_eq!(m.get(&"c"), Some(&6));
        assert_eq!(m.len(), 3);

        // Force spill past N = 4 boundary
        m.insert("d", 4);
        m.insert("e", 5);
        assert!(m.capacity() > 4);

        // Mutate values on the heap
        for (_key, val) in m.iter_mut() {
            *val += 100;
        }

        // Verify heap mutations are applied correctly
        assert_eq!(m.get(&"a"), Some(&102));
        assert_eq!(m.get(&"b"), Some(&112));
        assert_eq!(m.get(&"c"), Some(&106));
        assert_eq!(m.get(&"d"), Some(&104));
        assert_eq!(m.get(&"e"), Some(&105));
        assert_eq!(m.len(), 5);
    }

    fn check_iter<I>(mut iter: I)
    where
        I: ExactSizeIterator,
        <I as Iterator>::Item: PartialEq + Debug,
    {
        let mut remaining = iter.len();
        assert_eq!(iter.size_hint(), (remaining, Some(remaining)));

        while remaining > 0 {
            assert!(iter.next().is_some());
            remaining -= 1;
            assert_eq!(iter.len(), remaining);
            assert_eq!(iter.size_hint(), (remaining, Some(remaining)));
        }

        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_iterator_exact_size_and_exhaustion() {
        // Inline immutable iterator.
        let mut map = EcoMap::<i32, i32, 4>::new();
        for i in 0..3 {
            map.insert(i, i * 10);
        }
        check_iter(map.iter());

        // Spilled immutable iterator.
        let mut map = EcoMap::<i32, i32, 4>::new();
        for i in 0..10 {
            map.insert(i, i * 10);
        }
        assert!(map.capacity() > 4);
        check_iter(map.iter());
    }

    #[test]
    fn test_iterator_mut_exact_size_and_exhaustion() {
        // Inline mutable iterator.
        let mut map = EcoMap::<i32, i32, 4>::new();
        for i in 0..3 {
            map.insert(i, i * 10);
        }
        check_iter(map.iter_mut());

        // Spilled mutable iterator.
        let mut map = EcoMap::<i32, i32, 4>::new();
        for i in 0..10 {
            map.insert(i, i * 10);
        }
        assert!(map.capacity() > 4);
        check_iter(map.iter_mut());
    }

    #[test]
    fn test_into_iter_exact_size_and_exhaustion() {
        // Inline owning iterator.
        let mut map = EcoMap::<i32, i32, 4>::new();
        for i in 0..3 {
            map.insert(i, i * 10);
        }
        check_iter(map.into_iter());

        // Spilled owning iterator.
        let mut map = EcoMap::<i32, i32, 4>::new();
        for i in 0..10 {
            map.insert(i, i * 10);
        }
        assert!(map.capacity() > 4);
        check_iter(map.into_iter());
    }

    #[test]
    fn test_drain() {
        // Inline map
        let mut map = EcoMap::<i32, i32, 4>::new();
        map.insert(1, 10);
        map.insert(2, 20);
        assert_eq!(map.len(), 2);

        let mut drained: Vec<_> = map.drain().collect();
        drained.sort_by_key(|(k, _)| *k);
        assert_eq!(drained, vec![(1, 10), (2, 20)]);
        assert_eq!(map.len(), 0);
        assert!(map.is_empty());
        assert_eq!(map.capacity(), 4); // Inline capacity remains N

        // Spilled map
        let mut map = EcoMap::<i32, i32, 4>::new();
        for i in 0..10 {
            map.insert(i, i * 10);
        }
        assert!(map.capacity() > 4);
        assert_eq!(map.len(), 10);

        let mut drained: Vec<_> = map.drain().collect();
        drained.sort_by_key(|(k, _)| *k);
        assert_eq!(drained, (0..10).map(|i| (i, i * 10)).collect::<Vec<_>>());
        assert_eq!(map.len(), 0);
        assert!(map.is_empty());
        // Capacity might change after drain depending on HashMap's shrink behavior
        // but it should still be usable.
        map.insert(100, 1000);
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn test_retain() {
        // Inline map
        let mut map = EcoMap::<i32, i32, 4>::new();
        map.insert(1, 10);
        map.insert(2, 20);
        map.insert(3, 30);
        map.insert(4, 40); // Fill inline capacity

        map.retain(|k, v| *k % 2 == 0 && *v > 25); // Keep even keys with value > 25
        assert_eq!(map.len(), 1);
        assert!(map.get(&2).is_none());
        assert!(map.get(&1).is_none());
        assert!(map.get(&3).is_none());
        assert_eq!(map.get(&4), Some(&40));

        // Spilled map
        let mut map = EcoMap::<i32, i32, 4>::new();
        for i in 0..10 {
            map.insert(i, i * 10);
        }
        assert!(map.capacity() > 4);

        map.retain(|k, v| *k % 3 == 0 || *v > 50); // Keep multiples of 3 or value > 50
        let mut pairs: Vec<_> = map.iter().collect();
        pairs.sort_by_key(|(k, _)| *k);

        assert_eq!(pairs.len(), 6);
        assert_eq!(pairs[0], (&0, &0)); // 0 % 3 == 0
        assert_eq!(pairs[1], (&3, &30)); // 3 % 3 == 0
        assert_eq!(pairs[2], (&6, &60)); // 6 % 3 == 0 (&& 60 > 50)
        assert_eq!(pairs[3], (&7, &70)); // 70 > 50
        assert_eq!(pairs[4], (&8, &80)); // 80 > 50
        assert_eq!(pairs[5], (&9, &90)); // 9 % 3 == 0 (&& 90 > 50)
    }

    #[test]
    fn test_retain_panic_safety() {
        use std::panic;

        let mut map = EcoMap::<_, _>::new();
        map.insert(1, "keep");
        map.insert(2, "panic");
        map.insert(3, "keep");

        let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
            map.retain(|&k, _| {
                if k == 2 {
                    panic!("intentional panic");
                }
                true
            });
        }));

        assert!(result.is_err());
        assert!(map.len() <= 3);
        assert!(map.get(&1).is_some());
    }

    #[test]
    fn test_partial_eq() {
        // Empty maps are equal
        let a: EcoMap<i32, i32, 4> = EcoMap::new();
        let b: EcoMap<i32, i32, 4> = EcoMap::new();
        assert_eq!(a, b);

        // Same key-value pairs inline
        let mut a = EcoMap::<i32, i32, 4>::new();
        let mut b = EcoMap::<i32, i32, 4>::new();
        a.insert(1, 10);
        a.insert(2, 20);
        b.insert(1, 10);
        b.insert(2, 20);
        assert_eq!(a, b);

        // Order doesn't matter
        let mut a = EcoMap::<i32, i32, 4>::new();
        let mut b = EcoMap::<i32, i32, 4>::new();
        a.insert(1, 10);
        a.insert(2, 20);
        b.insert(2, 20);
        b.insert(1, 10);
        assert_eq!(a, b);

        // Different values
        let mut a = EcoMap::<i32, i32, 4>::new();
        let mut b = EcoMap::<i32, i32, 4>::new();
        a.insert(1, 10);
        b.insert(1, 99);
        assert_ne!(a, b);

        // Different keys
        let mut a = EcoMap::<i32, i32, 4>::new();
        let mut b = EcoMap::<i32, i32, 4>::new();
        a.insert(1, 10);
        b.insert(2, 10);
        assert_ne!(a, b);

        // Different lengths
        let mut a = EcoMap::<i32, i32, 4>::new();
        let mut b = EcoMap::<i32, i32, 4>::new();
        a.insert(1, 10);
        a.insert(2, 20);
        b.insert(1, 10);
        assert_ne!(a, b);

        // Spilled: equal
        let mut a = EcoMap::<i32, i32, 4>::new();
        let mut b = EcoMap::<i32, i32, 4>::new();
        for i in 0..10 {
            a.insert(i, i * 10);
            b.insert(i, i * 10);
        }
        assert!(a.capacity() > 4);
        assert!(b.capacity() > 4);
        assert_eq!(a, b);

        // Spilled: not equal
        let mut b = EcoMap::<i32, i32, 4>::new();
        for i in 0..10 {
            b.insert(i, i * 100);
        }
        assert_ne!(a, b);

        // Inline vs Spilled with same content are equal
        let mut inline = EcoMap::<i32, i32, 4>::new();
        for i in 0..3 {
            inline.insert(i, i);
        }
        let mut spilled = EcoMap::<i32, i32, 4>::new();
        for i in 0..10 {
            spilled.insert(i, i);
        }
        for i in 3..10 {
            spilled.remove(&i);
        }
        spilled.shrink_to_fit();
        assert_eq!(spilled.capacity(), 4);
        assert_eq!(inline, spilled);
    }

    #[test]
    fn test_debug() {
        // Helper: parse debug map output into a sorted vector of pair strings.
        fn sorted_pairs(debug_str: &str) -> Vec<String> {
            assert!(debug_str.starts_with('{'), "should start with {{: got {debug_str}");
            assert!(debug_str.ends_with('}'), "should end with }}: got {debug_str}");
            if debug_str == "{}" {
                return vec![];
            }
            let inner = &debug_str[1..debug_str.len() - 1];
            let mut pairs: Vec<String> =
                inner.split(", ").map(|s| s.to_string()).collect();
            pairs.sort();
            pairs
        }

        // Empty map
        assert_eq!(format!("{:?}", EcoMap::<i32, i32, 4>::new()), "{}");

        // Single entry
        let mut map = EcoMap::<i32, i32, 4>::new();
        map.insert(1, 10);
        assert_eq!(sorted_pairs(&format!("{:?}", map)), vec!["1: 10"]);

        // Multiple entries inline (order doesn't matter via sorted_pairs)
        let mut map = EcoMap::<i32, i32, 4>::new();
        map.insert(1, 10);
        map.insert(2, 20);
        map.insert(3, 30);
        assert_eq!(sorted_pairs(&format!("{:?}", map)), vec!["1: 10", "2: 20", "3: 30"]);

        // Spilled map
        let mut map = EcoMap::<i32, i32, 4>::new();
        for i in 0..10 {
            map.insert(i, i * 10);
        }
        assert!(map.capacity() > 4);
        let expected: Vec<String> = (0..10).map(|i| format!("{i}: {}", i * 10)).collect();
        assert_eq!(sorted_pairs(&format!("{:?}", map)), expected);

        // String keys/values
        let mut map = EcoMap::<String, String, 4>::new();
        map.insert("a".into(), "alpha".into());
        map.insert("b".into(), "beta".into());
        let mut expected = vec!["\"a\": \"alpha\"", "\"b\": \"beta\""];
        expected.sort();
        assert_eq!(sorted_pairs(&format!("{:?}", map)), expected);
    }

    #[test]
    fn test_clear_inline_and_spilled() {
        // Inline
        let mut m = EcoMap::<i32, i32, 4>::new();
        m.insert(1, 10);
        m.insert(2, 20);
        assert_eq!(m.len(), 2);

        m.clear();
        assert_eq!(m.len(), 0);
        assert!(m.is_empty());
        assert_eq!(m.get(&1), None);
        assert_eq!(m.get(&2), None);

        // Re-insert into the cleared inline map to ensure state integrity
        m.insert(1, 100);
        assert_eq!(m.get(&1), Some(&100));
        assert_eq!(m.len(), 1);

        // Force a spill by exceeding N = 4 capacity
        for i in 0..10 {
            m.insert(i, i * 10);
        }
        assert!(m.capacity() > 4);
        assert_eq!(m.len(), 10);

        // Clear the spilled map
        m.clear();
        assert_eq!(m.len(), 0);
        assert!(m.is_empty());

        // Ensure all heap keys are completely unreachable
        for i in 0..10 {
            assert_eq!(m.get(&i), None);
        }

        // Shrink it back down to verify that the cleared heap map
        // cleanly transitions back inline without carrying over ghosts
        m.shrink_to_fit();
        assert_eq!(m.capacity(), 4);
        assert_eq!(m.len(), 0);
    }
}
