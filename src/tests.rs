use super::*;

fn b<T>(value: T) -> Box<T> {
    Box::new(value)
}

#[test]
fn test_vec_macro() {
    assert_eq!(eco_vec![Box::new(1); 3], vec![Box::new(1); 3]);
}

#[test]
fn test_vec_aliased() {
    let mut first = EcoVec::new();
    first.push(1);
    first.push(2);
    first.push(3);
    assert_eq!(first.len(), 3);
    let mut second = first.clone();
    second.push(4);
    assert_eq!(second.len(), 4);
    assert_eq!(second, [1, 2, 3, 4]);
    assert_eq!(first, [1, 2, 3]);
}

#[test]
fn test_vec_into_iter() {
    let first = eco_vec![b(2), b(4), b(5)];
    let mut second = first.clone();
    assert_eq!(first.clone().into_iter().count(), 3);
    assert_eq!(second.clone().into_iter().rev().collect::<Vec<_>>(), [b(5), b(4), b(2)]);
    second.clear();
    assert_eq!(second.into_iter().collect::<Vec<_>>(), []);
    assert_eq!(first.clone().into_iter().collect::<Vec<_>>(), [b(2), b(4), b(5)]);
    let mut iter = first.into_iter();
    assert_eq!(iter.next(), Some(b(2)));
    assert_eq!(iter.as_slice(), [b(4), b(5)]);
    drop(iter);
}

#[test]
fn test_vec_mutations() {
    let mut vec: EcoVec<&'static str> =
        "hello, world! what's going on?".split_whitespace().collect();

    assert_eq!(vec.len(), 5);
    assert_eq!(vec.capacity(), 8);
    assert_eq!(vec, ["hello,", "world!", "what's", "going", "on?"]);
    assert_eq!(vec.pop(), Some("on?"));
    assert_eq!(vec.len(), 4);
    assert_eq!(vec.last(), Some(&"going"));
    assert_eq!(vec.remove(1), "world!");
    assert_eq!(vec.len(), 3);
    assert_eq!(vec, ["hello,", "what's", "going"]);
    assert_eq!(vec[1], "what's");
    vec.push("where?");
    vec.insert(1, "wonder!");
    assert_eq!(vec, ["hello,", "wonder!", "what's", "going", "where?"]);
    vec.retain(|s| s.starts_with("w"));
    assert_eq!(vec, ["wonder!", "what's", "where?"]);
    vec.truncate(1);
    assert_eq!(vec.last(), vec.first());
}

#[test]
fn test_vec_extend() {
    let mut vec = EcoVec::new();
    vec.extend_from_byte_slice(&[2, 3, 4]);
    assert_eq!(vec, [2, 3, 4]);
}

const ALPH: &str = "abcdefghijklmnopqrstuvwxyz";

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
    v.push_str("efghij");
    assert_eq!(v.len(), LIMIT);

    // Test spilling with `push`.
    let mut a = v.clone();
    assert_eq!(a, "abcd😀efghij");
    a.push('k');
    assert_eq!(a, "abcd😀efghijk");
    assert_eq!(a.len(), 15);

    // Test spilling with `push_str`.
    let mut b = v.clone();
    b.push_str("klmn");
    assert_eq!(b, "abcd😀efghijklmn");
    assert_eq!(b.len(), 18);

    // v should be unchanged.
    assert_eq!(v.len(), LIMIT);
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
