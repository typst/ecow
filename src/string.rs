use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt::{self, Debug, Display, Formatter, Write};
use std::hash::{Hash, Hasher};
use std::ops::{Add, AddAssign, Deref};

use super::EcoVec;

/// Create a new [`EcoString`] from a format string.
/// ```
/// # use ecow::format_eco;
/// assert_eq!(format_eco!("Hello, {}!", 123), "Hello, 123!");
/// ```
#[macro_export]
macro_rules! format_eco {
    ($($tts:tt)*) => {{
        use ::std::fmt::Write;
        let mut s = $crate::EcoString::new();
        ::std::write!(s, $($tts)*).unwrap();
        s
    }};
}

/// An economical string with inline storage and clone-on-write semantics.
///
/// This type has a size of 16 bytes and is null-pointer optimized (meaning that
/// `Option<EcoString>` also takes 16 bytes). It has 14 bytes of inline storage
/// and starting from 15 bytes it becomes an `EcoVec<u8>`.
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
/// let big = small + " to planet earth! 🌱";
/// let mut third = big.clone();
/// assert_eq!(third, "Welcome to planet earth! 🌱");
///
/// // This allocates again to mutate `third` without affecting `big`.
/// assert_eq!(third.pop(), Some('🌱'));
/// assert_eq!(big, "Welcome to planet earth! 🌱");
/// ```
#[derive(Clone)]
pub struct EcoString(Repr);

/// The internal representation. Either:
/// - inline when below a certain number of bytes, or
/// - reference-counted on the heap with clone-on-write semantics.
#[derive(Clone)]
enum Repr {
    /// Invariant: len <= LIMIT.
    Small {
        buf: [u8; LIMIT],
        len: u8,
    },
    Large(EcoVec<u8>),
}

/// The maximum number of bytes that can be stored inline.
///
/// The value is chosen such that an `EcoString` fits exactly into 16 bytes
/// (which are needed anyway due to the `Arc`s alignment, at least on 64-bit
/// platforms).
///
/// Must be at least 4 to hold any char.
pub(crate) const LIMIT: usize = 14;

impl EcoString {
    /// Create a new, empty string.
    pub const fn new() -> Self {
        Self(Repr::Small { buf: [0; LIMIT], len: 0 })
    }

    /// Create a new, empty string with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        if capacity <= LIMIT {
            Self::new()
        } else {
            Self(Repr::Large(EcoVec::with_capacity(capacity)))
        }
    }

    /// Create an instance from an existing string-like type.
    fn from_str_like(string: impl AsRef<str>) -> Self {
        let string = string.as_ref();
        let len = string.len();
        let mut buf = [0; LIMIT];
        Self(if let Some(head) = buf.get_mut(..len) {
            // We maintain `len < LIMIT` because `get_mut` succeeded.
            head.copy_from_slice(string.as_bytes());
            Repr::Small { buf, len: len as u8 }
        } else {
            Repr::Large(string.as_bytes().into())
        })
    }

    /// Whether the string is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The length of the string in bytes.
    pub fn len(&self) -> usize {
        match &self.0 {
            Repr::Small { len, .. } => usize::from(*len),
            Repr::Large(string) => string.len(),
        }
    }

    /// A string slice containing the entire string.
    pub fn as_str(&self) -> &str {
        let buf = match &self.0 {
            Repr::Small { buf, len } => {
                // Safety:
                // We have the invariant len <= LIMIT.
                unsafe { buf.get_unchecked(..usize::from(*len)) }
            }
            Repr::Large(vec) => &vec,
        };

        // Safety:
        // The buffer contents stem from correct UTF-8 sources:
        // - Valid ASCII characters
        // - Other string slices
        // - Chars that were encoded with char::encode_utf8
        unsafe { std::str::from_utf8_unchecked(buf) }
    }

    /// Append the given character at the end.
    pub fn push(&mut self, c: char) {
        if c.len_utf8() == 1 {
            match &mut self.0 {
                Repr::Small { buf, len } => {
                    let prev = usize::from(*len);
                    if let Some(slot) = buf.get_mut(prev) {
                        // We maintain `len < LIMIT` because `get_mut` succeeded.
                        *slot = c as u8;
                        *len += 1;
                    } else {
                        debug_assert_eq!(prev, LIMIT);
                        let mut vec = EcoVec::with_capacity(prev + 1);
                        vec.extend_from_byte_slice(buf);
                        vec.push(c as u8);
                        self.0 = Repr::Large(vec);
                    }
                }
                Repr::Large(vec) => vec.push(c as u8),
            }
        } else {
            self.push_str(c.encode_utf8(&mut [0; 4]));
        }
    }

    /// Append the given string slice at the end.
    pub fn push_str(&mut self, string: &str) {
        match &mut self.0 {
            Repr::Small { buf, len } => {
                let prev = usize::from(*len);
                let new = prev + string.len();
                if let Some(segment) = buf.get_mut(prev..new) {
                    // We maintain `len < LIMIT` because `get_mut` succeeded.
                    segment.copy_from_slice(string.as_bytes());
                    *len = new as u8;
                } else {
                    // Safety: See `Self::as_str()`.
                    let existing = unsafe { buf.get_unchecked(..prev) };
                    let mut vec = EcoVec::with_capacity(prev + string.len());
                    vec.extend_from_byte_slice(existing);
                    vec.extend_from_byte_slice(string.as_bytes());
                    self.0 = Repr::Large(vec);
                }
            }
            Repr::Large(vec) => vec.extend_from_byte_slice(string.as_bytes()),
        }
    }

    /// Remove the last character from the string.
    pub fn pop(&mut self) -> Option<char> {
        let c = self.as_str().chars().rev().next()?;
        let len_utf8 = c.len_utf8();

        // Will not underflow because the char was decoded from the buffer.
        match &mut self.0 {
            Repr::Small { len, .. } => *len -= len_utf8 as u8,
            Repr::Large(vec) => vec.truncate(vec.len() - len_utf8),
        }

        Some(c)
    }

    /// Clear the string.
    pub fn clear(&mut self) {
        match &mut self.0 {
            Repr::Small { len, .. } => *len = 0,
            Repr::Large(vec) => vec.clear(),
        }
    }

    /// Convert the string to lowercase.
    pub fn to_lowercase(&self) -> Self {
        if let Repr::Small { mut buf, len } = self.0 {
            if self.is_ascii() {
                buf[..usize::from(len)].make_ascii_lowercase();
                return Self(Repr::Small { buf, len });
            }
        }

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

    /// Convert the string to uppercase.
    pub fn to_uppercase(&self) -> Self {
        if let Repr::Small { mut buf, len } = self.0 {
            if self.is_ascii() {
                buf[..usize::from(len)].make_ascii_uppercase();
                return Self(Repr::Small { buf, len });
            }
        }

        let str = self.as_str();
        let mut upper = Self::with_capacity(str.len());
        for c in str.chars() {
            for v in c.to_uppercase() {
                upper.push(v);
            }
        }

        upper
    }

    /// Repeat this string `n` times.
    pub fn repeat(&self, n: usize) -> Self {
        if n == 0 {
            return Self::new();
        }

        if let Repr::Small { buf, len } = self.0 {
            let prev = usize::from(len);
            let new = prev.saturating_mul(n);
            if new <= LIMIT {
                let src = &buf[..prev];
                let mut buf = [0; LIMIT];
                for i in 0..n {
                    buf[prev * i..prev * (i + 1)].copy_from_slice(src);
                }

                // We maintain `len < LIMIT` because of the check above.
                return Self(Repr::Small { buf, len: new as u8 });
            }
        }

        let slice = self.as_bytes();
        let capacity = slice.len().saturating_mul(n);
        let mut vec = EcoVec::with_capacity(capacity);
        for _ in 0..n {
            vec.extend_from_byte_slice(slice);
        }

        Self(Repr::Large(vec))
    }
}

impl Deref for EcoString {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl Default for EcoString {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for EcoString {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self.as_str(), f)
    }
}

impl Display for EcoString {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self.as_str(), f)
    }
}

impl Eq for EcoString {}

impl PartialEq for EcoString {
    fn eq(&self, other: &Self) -> bool {
        self.as_str().eq(other.as_str())
    }
}

impl PartialEq<str> for EcoString {
    fn eq(&self, other: &str) -> bool {
        self.as_str().eq(other)
    }
}

impl PartialEq<&str> for EcoString {
    fn eq(&self, other: &&str) -> bool {
        self.as_str().eq(*other)
    }
}

impl PartialEq<String> for EcoString {
    fn eq(&self, other: &String) -> bool {
        self.as_str().eq(other)
    }
}

impl PartialEq<EcoString> for str {
    fn eq(&self, other: &EcoString) -> bool {
        self.eq(other.as_str())
    }
}

impl PartialEq<EcoString> for &str {
    fn eq(&self, other: &EcoString) -> bool {
        (*self).eq(other.as_str())
    }
}

impl PartialEq<EcoString> for String {
    fn eq(&self, other: &EcoString) -> bool {
        self.eq(other.as_str())
    }
}

impl Ord for EcoString {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl PartialOrd for EcoString {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

impl Hash for EcoString {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl Write for EcoString {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_str(s);
        Ok(())
    }

    fn write_char(&mut self, c: char) -> fmt::Result {
        self.push(c);
        Ok(())
    }
}

impl Add for EcoString {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl AddAssign for EcoString {
    fn add_assign(&mut self, rhs: Self) {
        self.push_str(rhs.as_str());
    }
}

impl Add<&str> for EcoString {
    type Output = Self;

    fn add(mut self, rhs: &str) -> Self::Output {
        self += rhs;
        self
    }
}

impl AddAssign<&str> for EcoString {
    fn add_assign(&mut self, rhs: &str) {
        self.push_str(rhs);
    }
}

impl AsRef<str> for EcoString {
    fn as_ref(&self) -> &str {
        self
    }
}

impl Borrow<str> for EcoString {
    fn borrow(&self) -> &str {
        self
    }
}

impl From<char> for EcoString {
    fn from(c: char) -> Self {
        // We maintain `len < LIMIT` because `LIMIT >= 4`.
        let mut buf = [0; LIMIT];
        let len = c.encode_utf8(&mut buf).len();
        Self(Repr::Small { buf, len: len as u8 })
    }
}

impl From<&str> for EcoString {
    fn from(s: &str) -> Self {
        Self::from_str_like(s)
    }
}

impl From<String> for EcoString {
    /// When the string does not fit inline, this needs to allocate to change
    /// the layout.
    fn from(s: String) -> Self {
        Self::from_str_like(s)
    }
}

impl FromIterator<char> for EcoString {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let mut s = Self::new();
        for c in iter {
            s.push(c);
        }
        s
    }
}

impl FromIterator<Self> for EcoString {
    fn from_iter<T: IntoIterator<Item = Self>>(iter: T) -> Self {
        let mut s = Self::new();
        for piece in iter {
            s.push_str(&piece);
        }
        s
    }
}

impl Extend<char> for EcoString {
    fn extend<T: IntoIterator<Item = char>>(&mut self, iter: T) {
        for c in iter {
            self.push(c);
        }
    }
}

impl From<EcoString> for String {
    /// This needs to allocate to change the layout.
    fn from(s: EcoString) -> Self {
        s.as_str().to_owned()
    }
}

impl From<&EcoString> for String {
    fn from(s: &EcoString) -> Self {
        s.as_str().to_owned()
    }
}
