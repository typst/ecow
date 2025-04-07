//! A clone-on-write, small-string-optimized alternative to [`String`].

use alloc::borrow::Cow;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::{self, Debug, Display, Formatter, Write};
use core::hash::{Hash, Hasher};
use core::ops::{Add, AddAssign, Deref};

#[cfg(not(feature = "std"))]
use alloc::string::String;

use crate::dynamic::{DynamicVec, InlineVec};

/// Create a new [`EcoString`] from a format string.
/// ```
/// # use ecow::eco_format;
/// assert_eq!(eco_format!("Hello, {}!", 123), "Hello, 123!");
/// ```
#[macro_export]
macro_rules! eco_format {
    ($($tts:tt)*) => {{
        use ::std::fmt::Write;
        let mut s = $crate::EcoString::new();
        ::std::write!(s, $($tts)*).unwrap();
        s
    }};
}

/// An economical string with inline storage and clone-on-write semantics.
///
/// This type has a size of 16 bytes. It has 15 bytes of inline storage and
/// starting from 16 bytes it becomes an [`EcoVec<u8>`](super::EcoVec). The
/// internal reference counter of the heap variant is atomic, making this type
/// [`Sync`] and [`Send`].
///
/// # Example
/// ```
/// use ecow::EcoString;
///
/// // This is stored inline.
/// let small = EcoString::from("Welcome");
///
/// // This spills to the heap only once: `big` and `third` share the same
/// // underlying allocation. Just like vectors, heap strings are only really
/// // cloned upon mutation.
/// let big = small + " to earth! 🌱";
/// let mut third = big.clone();
/// assert_eq!(big, "Welcome to earth! 🌱");
/// assert_eq!(third, big);
///
/// // This allocates again to mutate `third` without affecting `big`.
/// assert_eq!(third.pop(), Some('🌱'));
/// assert_eq!(third, "Welcome to earth! ");
/// assert_eq!(big, "Welcome to earth! 🌱");
/// ```
///
/// # Note
/// The above holds true for normal 32-bit or 64-bit little endian systems. On
/// 64-bit big-endian systems, the type's size increases to 24 bytes and the
/// amount of inline storage to 23 bytes.
#[derive(Clone)]
pub struct EcoString(DynamicVec);

impl EcoString {
    /// Maximum number of bytes for an inline `EcoString` before spilling on
    /// the heap.
    ///
    /// The exact value for this is architecture dependent.
    ///
    /// # Note
    /// This value is semver exempt and can be changed with any update.
    pub const INLINE_LIMIT: usize = crate::dynamic::LIMIT;

    /// Create a new, empty string.
    #[inline]
    pub const fn new() -> Self {
        Self(DynamicVec::new())
    }

    /// Create a new, inline string.
    ///
    /// Panics if the string's length exceeds the capacity of the inline
    /// storage.
    #[inline]
    pub const fn inline(string: &str) -> Self {
        let Ok(inline) = InlineVec::from_slice(string.as_bytes()) else {
            exceeded_inline_capacity();
        };
        Self(DynamicVec::from_inline(inline))
    }

    /// Create a new, empty string with the given `capacity`.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self(DynamicVec::with_capacity(capacity))
    }

    /// Create an instance from a string slice.
    #[inline]
    fn from_str(string: &str) -> Self {
        Self(DynamicVec::from_slice(string.as_bytes()))
    }

    /// Whether the string is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The length of the string in bytes.
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// A string slice containing the entire string.
    #[inline]
    pub fn as_str(&self) -> &str {
        // Safety:
        // The buffer contents stem from correct UTF-8 sources:
        // - Valid ASCII characters
        // - Other string slices
        // - Chars that were encoded with char::encode_utf8
        unsafe { core::str::from_utf8_unchecked(self.0.as_slice()) }
    }

    /// Produce a mutable slice containing the entire string.
    ///
    /// Clones the string if its reference count is larger than 1.
    #[inline]
    pub fn make_mut(&mut self) -> &mut str {
        // Safety:
        // The buffer contents stem from correct UTF-8 sources:
        // - Valid ASCII characters
        // - Other string slices
        // - Chars that were encoded with char::encode_utf8
        unsafe { core::str::from_utf8_unchecked_mut(self.0.make_mut()) }
    }

    /// Append the given character at the end.
    #[inline]
    pub fn push(&mut self, c: char) {
        if c.len_utf8() == 1 {
            self.0.push(c as u8);
        } else {
            self.push_str(c.encode_utf8(&mut [0; 4]));
        }
    }

    /// Append the given string slice at the end.
    pub fn push_str(&mut self, string: &str) {
        self.0.extend_from_slice(string.as_bytes());
    }

    /// Remove the last character from the string.
    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        let slice = self.as_str();
        let c = slice.chars().next_back()?;
        self.0.truncate(slice.len() - c.len_utf8());
        Some(c)
    }

    /// Clear the string.
    #[inline]
    pub fn clear(&mut self) {
        self.0.clear();
    }

    /// Shortens the string to the specified length.
    ///
    /// If `new_len` is greater than or equal to the string's current length,
    /// this has no effect.
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            self.0.truncate(new_len);
        }
    }

    /// Replaces all matches of a string with another string.
    ///
    /// This is a bit less general that [`str::replace`] because the `Pattern`
    /// trait is unstable. In return, it can produce an `EcoString` without
    /// any intermediate [`String`] allocation.
    pub fn replace(&self, pat: &str, to: &str) -> Self {
        self.replacen(pat, to, usize::MAX)
    }

    /// Replaces the first N matches of a string with another string.
    ///
    /// This is a bit less general that [`str::replacen`] because the `Pattern`
    /// trait is unstable. In return, it can produce an `EcoString` without
    /// any intermediate [`String`] allocation.
    pub fn replacen(&self, pat: &str, to: &str, count: usize) -> Self {
        // Copied from the standard library: https://github.com/rust-lang/rust
        let mut result = Self::new();
        let mut last_end = 0;
        for (start, part) in self.match_indices(pat).take(count) {
            // Safety: Copied from std.
            result.push_str(unsafe { self.get_unchecked(last_end..start) });
            result.push_str(to);
            last_end = start + part.len();
        }
        // Safety: Copied from std.
        result.push_str(unsafe { self.get_unchecked(last_end..self.len()) });
        result
    }

    /// Returns the lowercase equivalent of this string.
    pub fn to_lowercase(&self) -> Self {
        let str = self.as_str();
        let mut lower = Self::with_capacity(str.len());
        for c in str.chars() {
            // Let std handle the special case.
            if c == 'Σ' {
                return str.to_lowercase().into();
            }
            for v in c.to_lowercase() {
                lower.push(v);
            }
        }
        lower
    }

    /// Returns the uppercase equivalent of this string.
    pub fn to_uppercase(&self) -> Self {
        let str = self.as_str();
        let mut upper = Self::with_capacity(str.len());
        for c in str.chars() {
            for v in c.to_uppercase() {
                upper.push(v);
            }
        }
        upper
    }

    /// Returns a copy of this string where each character is mapped to its
    /// ASCII uppercase equivalent.
    pub fn to_ascii_lowercase(&self) -> Self {
        let mut s = self.clone();
        s.make_mut().make_ascii_lowercase();
        s
    }

    /// Returns a copy of this string where each character is mapped to its
    /// ASCII uppercase equivalent.
    pub fn to_ascii_uppercase(&self) -> Self {
        let mut s = self.clone();
        s.make_mut().make_ascii_uppercase();
        s
    }

    /// Repeat this string `n` times.
    pub fn repeat(&self, n: usize) -> Self {
        let slice = self.as_bytes();
        let capacity = slice.len().saturating_mul(n);
        let mut vec = DynamicVec::with_capacity(capacity);
        for _ in 0..n {
            vec.extend_from_slice(slice);
        }
        Self(vec)
    }
}

impl Deref for EcoString {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl Default for EcoString {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for EcoString {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self.as_str(), f)
    }
}

impl Display for EcoString {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self.as_str(), f)
    }
}

impl Eq for EcoString {}

impl PartialEq for EcoString {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_str().eq(other.as_str())
    }
}

impl PartialEq<str> for EcoString {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_str().eq(other)
    }
}

impl PartialEq<&str> for EcoString {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        self.as_str().eq(*other)
    }
}

impl PartialEq<String> for EcoString {
    #[inline]
    fn eq(&self, other: &String) -> bool {
        self.as_str().eq(other)
    }
}

impl PartialEq<EcoString> for str {
    #[inline]
    fn eq(&self, other: &EcoString) -> bool {
        self.eq(other.as_str())
    }
}

impl PartialEq<EcoString> for &str {
    #[inline]
    fn eq(&self, other: &EcoString) -> bool {
        (*self).eq(other.as_str())
    }
}

impl PartialEq<EcoString> for String {
    #[inline]
    fn eq(&self, other: &EcoString) -> bool {
        self.eq(other.as_str())
    }
}

impl Ord for EcoString {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl PartialOrd for EcoString {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for EcoString {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl Write for EcoString {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_str(s);
        Ok(())
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
        self.push(c);
        Ok(())
    }
}

impl Add for EcoString {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl AddAssign for EcoString {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.push_str(rhs.as_str());
    }
}

impl Add<&str> for EcoString {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: &str) -> Self::Output {
        self += rhs;
        self
    }
}

impl AddAssign<&str> for EcoString {
    #[inline]
    fn add_assign(&mut self, rhs: &str) {
        self.push_str(rhs);
    }
}

impl AsRef<str> for EcoString {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl Borrow<str> for EcoString {
    #[inline]
    fn borrow(&self) -> &str {
        self
    }
}

impl From<char> for EcoString {
    #[inline]
    fn from(c: char) -> Self {
        Self::inline(c.encode_utf8(&mut [0; 4]))
    }
}

impl From<&str> for EcoString {
    #[inline]
    fn from(s: &str) -> Self {
        Self::from_str(s)
    }
}

impl From<String> for EcoString {
    /// When the string does not fit inline, this needs to allocate to change
    /// the layout.
    #[inline]
    fn from(s: String) -> Self {
        Self::from_str(&s)
    }
}

impl From<&String> for EcoString {
    #[inline]
    fn from(s: &String) -> Self {
        Self::from_str(s.as_str())
    }
}

impl From<&EcoString> for EcoString {
    #[inline]
    fn from(s: &EcoString) -> Self {
        s.clone()
    }
}

impl From<Cow<'_, str>> for EcoString {
    #[inline]
    fn from(s: Cow<str>) -> Self {
        Self::from_str(&s)
    }
}

impl FromIterator<char> for EcoString {
    #[inline]
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let mut s = Self::new();
        for c in iter {
            s.push(c);
        }
        s
    }
}

impl FromIterator<Self> for EcoString {
    #[inline]
    fn from_iter<T: IntoIterator<Item = Self>>(iter: T) -> Self {
        let mut s = Self::new();
        for piece in iter {
            s.push_str(&piece);
        }
        s
    }
}

impl Extend<char> for EcoString {
    #[inline]
    fn extend<T: IntoIterator<Item = char>>(&mut self, iter: T) {
        for c in iter {
            self.push(c);
        }
    }
}

impl From<EcoString> for String {
    /// This needs to allocate to change the layout.
    #[inline]
    fn from(s: EcoString) -> Self {
        s.as_str().into()
    }
}

impl From<&EcoString> for String {
    #[inline]
    fn from(s: &EcoString) -> Self {
        s.as_str().into()
    }
}

#[cold]
const fn exceeded_inline_capacity() -> ! {
    panic!("exceeded inline capacity");
}

#[cfg(feature = "serde")]
mod serde {
    use crate::EcoString;
    use core::fmt;
    use serde::de::{Deserializer, Error, Unexpected, Visitor};

    impl serde::Serialize for EcoString {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            self.as_str().serialize(serializer)
        }
    }

    impl<'de> serde::Deserialize<'de> for EcoString {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            struct EcoStringVisitor;

            impl Visitor<'_> for EcoStringVisitor {
                type Value = EcoString;

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    formatter.write_str("a string")
                }

                fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
                where
                    E: Error,
                {
                    Ok(EcoString::from(v))
                }

                fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
                where
                    E: Error,
                {
                    if let Ok(utf8) = core::str::from_utf8(v) {
                        return Ok(EcoString::from(utf8));
                    }
                    Err(Error::invalid_value(Unexpected::Bytes(v), &self))
                }
            }

            deserializer.deserialize_str(EcoStringVisitor)
        }
    }
}
