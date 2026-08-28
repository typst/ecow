//! A clone-on-write byte buffer with inline storage.

use alloc::borrow::Cow;
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::{self, Debug, Formatter};
use core::hash::{Hash, Hasher};
use core::mem::{self, ManuallyDrop};
use core::ops::{Deref, RangeBounds};
use core::ptr;

use super::EcoVec;

/// An economical byte buffer with inline storage and clone-on-write semantics.
///
/// This type has a size of 16 bytes. It has 15 bytes of inline storage and,
/// starting at 16 bytes, spills into an [`EcoVec<u8>`]. The internal reference
/// counter of the heap variant is atomic, making this type [`Sync`] and
/// [`Send`].
///
/// # Example
/// ```
/// use ecow::EcoBytes;
///
/// // This is stored inline.
/// let small = EcoBytes::from(b"Welcome");
///
/// // This spills to the heap. The clone shares its allocation until mutation.
/// let mut big = small.repeat(3);
/// let clone = big.clone();
/// big.push(b'!');
/// assert_ne!(big, clone);
/// ```
///
/// # Note
/// The above holds true for normal 32-bit or 64-bit little-endian systems. On
/// 64-bit big-endian systems, the type's size increases to 24 bytes and the
/// amount of inline storage to 23 bytes.
pub struct EcoBytes(Repr);

/// The internal representation.
///
/// On 64-bit little endian, this assumes that no valid EcoVec exists in which
/// the highest-order bit of the InlineVec's `tagged_len` would be set. This is
/// true because EcoVec is repr(C) and its second field `len` is bounded by
/// `isize::MAX`. On 32-bit, it's no problem and for 64-bit big endian, we
/// have an increased limit to prevent the overlap.
#[repr(C)]
union Repr {
    inline: InlineVec,
    spilled: ManuallyDrop<EcoVec<u8>>,
}

/// This is never stored in memory, it's just an abstraction for safe access.
#[derive(Debug)]
enum Variant<'a> {
    Inline(&'a InlineVec),
    Spilled(&'a EcoVec<u8>),
}

/// This is never stored in memory, it's just an abstraction for safe access.
#[derive(Debug)]
enum VariantMut<'a> {
    Inline(&'a mut InlineVec),
    Spilled(&'a mut EcoVec<u8>),
}

/// The maximum amount of inline storage. Typically, this is 15 bytes.
///
/// However, in the rare exotic system, we still want things to be safe.
/// Therefore, the following special cases:
/// - For big endian, we increase the limit such that the tagged length of the
///   inline variants doesn't overlap with the EcoVec. For little endian, it's
///   fine since the highest order bit is never set for a valid EcoVec.
/// - In case somehow EcoVec is very big (128-bit pointers woah), increase the
///   limit too.
pub(crate) const LIMIT: usize = {
    let mut limit = 15;
    if limit < mem::size_of::<EcoVec<u8>>() - 1 {
        limit = mem::size_of::<EcoVec<u8>>() - 1;
    }
    if cfg!(target_endian = "big") {
        limit += mem::size_of::<usize>();
    }
    limit
};

/// This bit is used to check whether we are inline or not. On 64-bit little
/// endian, it coincides with the highest-order bit of an EcoVec's length, which
/// can't be set because the EcoVec's length never exceeds `isize::MAX`.
const LEN_TAG: u8 = 0b1000_0000;

/// This is used to mask off the tag to get the inline variant's length.
const LEN_MASK: u8 = 0b0111_1111;

impl EcoBytes {
    /// Maximum number of bytes for an inline `EcoBytes` before spilling to the
    /// heap.
    ///
    /// The exact value for this is architecture dependent.
    ///
    /// # Note
    /// This value is semver exempt and can be changed with any update.
    pub const INLINE_LIMIT: usize = LIMIT;

    /// Create a new, empty byte buffer.
    ///
    /// This does not allocate.
    #[inline]
    pub const fn new() -> Self {
        Self::from_inline(InlineVec::new())
    }

    /// Create a new, inline byte buffer.
    ///
    /// Panics if the slice's length exceeds the capacity of the inline storage.
    #[inline]
    pub const fn inline(bytes: &[u8]) -> Self {
        let Ok(inline) = InlineVec::from_slice(bytes) else {
            exceeded_inline_capacity();
        };
        Self::from_inline(inline)
    }

    /// Try to create a new, inline byte buffer.
    ///
    /// Returns `None` if the slice's length exceeds the capacity of the inline
    /// storage.
    #[inline]
    pub const fn try_inline(bytes: &[u8]) -> Option<Self> {
        match InlineVec::from_slice(bytes) {
            Ok(inline) => Some(Self::from_inline(inline)),
            Err(()) => None,
        }
    }

    #[inline]
    pub(crate) const fn from_inline(inline: InlineVec) -> Self {
        Self(Repr { inline })
    }

    #[inline]
    const fn from_eco(vec: EcoVec<u8>) -> Self {
        // Safety:
        // Explicitly set `tagged_len` to 0 to mark this as a spilled variant.
        // Just initializing with `Repr { spilled: ... }` would leave
        // `tagged_len` uninitialized, leading to undefined behaviour on access.
        let mut repr = Repr {
            inline: InlineVec { buf: [0; LIMIT], tagged_len: 0 },
        };
        repr.spilled = ManuallyDrop::new(vec);
        Self(repr)
    }

    /// Create a new, empty byte buffer with at least the specified capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        if capacity <= LIMIT {
            Self::new()
        } else {
            Self::from_eco(EcoVec::with_capacity(capacity))
        }
    }

    /// Returns `true` if the buffer contains no bytes.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The number of bytes in the buffer.
    #[inline]
    pub fn len(&self) -> usize {
        match self.variant() {
            Variant::Inline(inline) => inline.len(),
            Variant::Spilled(spilled) => spilled.len(),
        }
    }

    /// How many bytes the buffer can hold without allocating.
    ///
    /// If the buffer's heap allocation is shared, mutation can still allocate
    /// even when the requested length fits within this capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        match self.variant() {
            Variant::Inline(_) => LIMIT,
            Variant::Spilled(spilled) => spilled.capacity(),
        }
    }

    /// Extracts a slice containing the entire buffer.
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        match self.variant() {
            Variant::Inline(inline) => inline.as_slice(),
            Variant::Spilled(spilled) => spilled.as_slice(),
        }
    }

    /// Produce a mutable slice containing the entire buffer.
    ///
    /// Clones the buffer if its reference count is larger than 1.
    #[inline]
    pub fn make_mut(&mut self) -> &mut [u8] {
        match self.variant_mut() {
            VariantMut::Inline(inline) => inline.as_mut_slice(),
            VariantMut::Spilled(spilled) => spilled.make_mut(),
        }
    }

    /// Add a byte at the end of the buffer.
    ///
    /// Clones the buffer if its reference count is larger than 1.
    #[inline]
    pub fn push(&mut self, byte: u8) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => {
                if inline.push(byte).is_err() {
                    let capacity = EcoVec::<u8>::amortized_cap(inline.len(), 1, LIMIT);
                    let mut eco = EcoVec::with_capacity(capacity);
                    eco.extend_from_byte_slice(inline.as_slice());
                    eco.push(byte);
                    *self = Self::from_eco(eco);
                }
            }
            VariantMut::Spilled(spilled) => {
                spilled.push(byte);
            }
        }
    }

    /// Removes and returns the last byte, or returns `None` if the buffer is
    /// empty.
    ///
    /// Clones the buffer if its reference count is larger than 1.
    #[inline]
    pub fn pop(&mut self) -> Option<u8> {
        match self.variant_mut() {
            VariantMut::Inline(inline) => inline.pop(),
            VariantMut::Spilled(spilled) => spilled.pop(),
        }
    }

    /// Inserts a byte at an index within the buffer, shifting all bytes after it
    /// to the right.
    ///
    /// Clones the buffer if its reference count is larger than 1.
    ///
    /// Panics if `index > len`.
    pub fn insert(&mut self, index: usize, byte: u8) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => {
                if inline.insert(index, byte).is_err() {
                    let capacity = EcoVec::<u8>::amortized_cap(inline.len(), 1, LIMIT);
                    let mut eco = EcoVec::with_capacity(capacity);
                    eco.extend_from_byte_slice(inline.as_slice());
                    eco.insert(index, byte);
                    *self = Self::from_eco(eco);
                }
            }
            VariantMut::Spilled(spilled) => spilled.insert(index, byte),
        }
    }

    /// Removes and returns the byte at position index within the buffer,
    /// shifting all bytes after it to the left.
    ///
    /// Clones the buffer if its reference count is larger than 1.
    ///
    /// Panics if `index >= len`.
    pub fn remove(&mut self, index: usize) -> u8 {
        match self.variant_mut() {
            VariantMut::Inline(inline) => inline.remove(index),
            VariantMut::Spilled(spilled) => spilled.remove(index),
        }
    }

    /// Copies and pushes all bytes in a slice to the buffer.
    #[inline]
    pub fn extend_from_slice(&mut self, bytes: &[u8]) {
        if bytes.is_empty() {
            return;
        }

        match self.variant_mut() {
            VariantMut::Inline(inline) => {
                if inline.extend_from_slice(bytes).is_err() {
                    let needed = inline.len() + bytes.len();
                    let mut eco = EcoVec::with_capacity(needed.next_power_of_two());
                    eco.extend_from_byte_slice(inline.as_slice());
                    eco.extend_from_byte_slice(bytes);
                    *self = Self::from_eco(eco);
                }
            }
            VariantMut::Spilled(spilled) => {
                spilled.extend_from_byte_slice(bytes);
            }
        }
    }

    /// Inserts the given byte slice at the `index`.
    ///
    /// Clones the buffer if its reference count is larger than 1.
    #[inline]
    pub fn insert_slice(&mut self, index: usize, bytes: &[u8]) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => {
                if inline.insert_slice(index, bytes).is_err() {
                    let needed = inline.len() + bytes.len();
                    let mut eco = EcoVec::with_capacity(needed.next_power_of_two());
                    let (a, b) = inline.as_slice().split_at(index);
                    eco.extend_from_byte_slice(a);
                    eco.extend_from_byte_slice(bytes);
                    eco.extend_from_byte_slice(b);
                    *self = Self::from_eco(eco);
                }
            }
            VariantMut::Spilled(spilled) => {
                spilled.splice(index..index, bytes.iter().copied());
            }
        }
    }

    /// Removes all bytes from the buffer.
    #[inline]
    pub fn clear(&mut self) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => inline.clear(),
            VariantMut::Spilled(spilled) => spilled.clear(),
        }
    }

    /// Shortens the buffer, keeping the first `target` bytes and dropping the
    /// rest.
    ///
    /// Clones the buffer if its reference count is larger than 1 and
    /// `target < len`.
    #[inline]
    pub fn truncate(&mut self, target: usize) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => inline.truncate(target),
            VariantMut::Spilled(spilled) => spilled.truncate(target),
        }
    }

    /// Reserve space for at least `additional` more bytes.
    ///
    /// Guarantees that the resulting buffer has space for `additional` more
    /// bytes and, if spilled, uniquely owns its backing allocation.
    pub fn reserve(&mut self, additional: usize) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => {
                if additional > LIMIT - inline.len() {
                    let capacity =
                        EcoVec::<u8>::amortized_cap(inline.len(), additional, LIMIT);
                    let mut eco = EcoVec::with_capacity(capacity);
                    eco.extend_from_byte_slice(inline.as_slice());
                    *self = Self::from_eco(eco);
                }
            }
            VariantMut::Spilled(spilled) => spilled.reserve(additional),
        }
    }

    /// Repeat this byte buffer `n` times.
    pub fn repeat(&self, n: usize) -> Self {
        let capacity = self.len().saturating_mul(n);
        let mut bytes = Self::with_capacity(capacity);
        for _ in 0..n {
            bytes.extend_from_slice(self);
        }
        bytes
    }

    #[inline]
    pub(crate) fn remove_range<R>(&mut self, range: R)
    where
        R: RangeBounds<usize>,
    {
        match self.variant_mut() {
            VariantMut::Inline(inline) => inline.remove_range(range),
            VariantMut::Spilled(spilled) => {
                spilled.drain(range);
            }
        }
    }

    /// Whether this byte buffer is stored inline.
    // If this returns true, guarantees that `self.0.inline` is initialized.
    // Otherwise, guarantees that `self.0.spilled` is initialized.
    #[inline]
    pub fn is_inline(&self) -> bool {
        // Safety:
        // We always initialize tagged_len, even for the `EcoVec` variant. For
        // the inline variant the highest-order bit is always `1`. For the
        // spilled variant, it is initialized with `0` and cannot deviate from
        // that because the EcoVec's `len` field is bounded by `isize::MAX`. (At
        // least on 64-bit little endian; on 32-bit or big-endian the EcoVec
        // and tagged_len fields don't even overlap, meaning tagged_len stays at
        // its initial value.)
        unsafe { self.0.inline.tagged_len & LEN_TAG != 0 }
    }

    #[inline]
    fn variant(&self) -> Variant<'_> {
        unsafe {
            // Safety:
            // We access the respective variant only if the check passes.
            if self.is_inline() {
                Variant::Inline(&self.0.inline)
            } else {
                Variant::Spilled(&self.0.spilled)
            }
        }
    }

    #[inline]
    fn variant_mut(&mut self) -> VariantMut<'_> {
        unsafe {
            // Safety:
            // We access the respective variant only if the check passes.
            if self.is_inline() {
                VariantMut::Inline(&mut self.0.inline)
            } else {
                VariantMut::Spilled(&mut self.0.spilled)
            }
        }
    }
}

impl Clone for EcoBytes {
    #[inline]
    fn clone(&self) -> Self {
        match self.variant() {
            Variant::Inline(inline) => Self::from_inline(*inline),
            Variant::Spilled(spilled) => Self::from_eco(spilled.clone()),
        }
    }
}

impl Drop for EcoBytes {
    #[inline]
    fn drop(&mut self) {
        if let VariantMut::Spilled(spilled) = self.variant_mut() {
            unsafe {
                // Safety: We are guaranteed to have a valid `EcoVec`.
                ptr::drop_in_place(spilled);
            }
        }
    }
}

impl Default for EcoBytes {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for EcoBytes {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self.as_slice(), f)
    }
}

impl Hash for EcoBytes {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl Eq for EcoBytes {}

impl PartialEq for EcoBytes {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl PartialEq<[u8]> for EcoBytes {
    #[inline]
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<&[u8]> for EcoBytes {
    #[inline]
    fn eq(&self, other: &&[u8]) -> bool {
        self.as_slice() == *other
    }
}

impl<const N: usize> PartialEq<[u8; N]> for EcoBytes {
    #[inline]
    fn eq(&self, other: &[u8; N]) -> bool {
        self.as_slice() == other
    }
}

impl<const N: usize> PartialEq<&[u8; N]> for EcoBytes {
    #[inline]
    fn eq(&self, other: &&[u8; N]) -> bool {
        self.as_slice() == *other
    }
}

impl PartialEq<Vec<u8>> for EcoBytes {
    #[inline]
    fn eq(&self, other: &Vec<u8>) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<EcoBytes> for [u8] {
    #[inline]
    fn eq(&self, other: &EcoBytes) -> bool {
        self == other.as_slice()
    }
}

impl<const N: usize> PartialEq<EcoBytes> for [u8; N] {
    #[inline]
    fn eq(&self, other: &EcoBytes) -> bool {
        self == other.as_slice()
    }
}

impl PartialEq<EcoBytes> for Vec<u8> {
    #[inline]
    fn eq(&self, other: &EcoBytes) -> bool {
        self == other.as_slice()
    }
}

impl PartialEq<EcoVec<u8>> for EcoBytes {
    #[inline]
    fn eq(&self, other: &EcoVec<u8>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl PartialEq<EcoBytes> for EcoVec<u8> {
    #[inline]
    fn eq(&self, other: &EcoBytes) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Ord for EcoBytes {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl PartialOrd for EcoBytes {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Deref for EcoBytes {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl Borrow<[u8]> for EcoBytes {
    #[inline]
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl AsRef<[u8]> for EcoBytes {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl From<&[u8]> for EcoBytes {
    #[inline]
    fn from(bytes: &[u8]) -> Self {
        match InlineVec::from_slice(bytes) {
            Ok(inline) => Self::from_inline(inline),
            Err(()) => Self::from_eco(EcoVec::from(bytes)),
        }
    }
}

impl<const N: usize> From<&[u8; N]> for EcoBytes {
    #[inline]
    fn from(bytes: &[u8; N]) -> Self {
        Self::from(bytes.as_slice())
    }
}

impl<const N: usize> From<[u8; N]> for EcoBytes {
    #[inline]
    fn from(bytes: [u8; N]) -> Self {
        Self::from(bytes.as_slice())
    }
}

impl From<Vec<u8>> for EcoBytes {
    /// When the bytes do not fit inline, this needs to allocate to change the
    /// layout.
    #[inline]
    fn from(bytes: Vec<u8>) -> Self {
        if bytes.len() <= LIMIT {
            Self::inline(&bytes)
        } else {
            Self::from_eco(EcoVec::from(bytes))
        }
    }
}

impl From<&Vec<u8>> for EcoBytes {
    #[inline]
    fn from(bytes: &Vec<u8>) -> Self {
        Self::from(bytes.as_slice())
    }
}

impl From<EcoVec<u8>> for EcoBytes {
    /// This does not allocate. The resulting byte buffer remains spilled even
    /// if its contents would fit inline.
    #[inline]
    fn from(bytes: EcoVec<u8>) -> Self {
        Self::from_eco(bytes)
    }
}

impl From<&EcoBytes> for EcoBytes {
    #[inline]
    fn from(bytes: &EcoBytes) -> Self {
        bytes.clone()
    }
}

impl From<Cow<'_, [u8]>> for EcoBytes {
    #[inline]
    fn from(bytes: Cow<[u8]>) -> Self {
        Self::from(&*bytes)
    }
}

impl From<EcoBytes> for Vec<u8> {
    /// This needs to allocate to change the layout.
    #[inline]
    fn from(bytes: EcoBytes) -> Self {
        bytes.as_slice().into()
    }
}

impl From<EcoBytes> for EcoVec<u8> {
    /// When the byte buffer is stored inline, this needs to allocate to change
    /// the layout. Otherwise, it reuses the existing allocation.
    #[inline]
    fn from(mut bytes: EcoBytes) -> Self {
        match bytes.variant_mut() {
            VariantMut::Inline(inline) => EcoVec::from(inline.as_slice()),
            VariantMut::Spilled(spilled) => mem::take(spilled),
        }
    }
}

impl From<&EcoBytes> for Vec<u8> {
    #[inline]
    fn from(bytes: &EcoBytes) -> Self {
        bytes.as_slice().into()
    }
}

impl From<&EcoBytes> for EcoVec<u8> {
    #[inline]
    fn from(bytes: &EcoBytes) -> Self {
        match bytes.variant() {
            Variant::Inline(inline) => inline.as_slice().into(),
            Variant::Spilled(spilled) => spilled.clone(),
        }
    }
}

impl FromIterator<u8> for EcoBytes {
    fn from_iter<I: IntoIterator<Item = u8>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut bytes = Self::with_capacity(iter.size_hint().0);
        bytes.extend(iter);
        bytes
    }
}

impl Extend<u8> for EcoBytes {
    fn extend<I: IntoIterator<Item = u8>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        let hint = iter.size_hint().0;
        if hint > 0 {
            self.reserve(hint);
        }
        for byte in iter {
            self.push(byte);
        }
    }
}

impl<'a> Extend<&'a u8> for EcoBytes {
    fn extend<I: IntoIterator<Item = &'a u8>>(&mut self, iter: I) {
        self.extend(iter.into_iter().copied());
    }
}

impl<'a> IntoIterator for &'a EcoBytes {
    type IntoIter = core::slice::Iter<'a, u8>;
    type Item = &'a u8;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub(crate) struct InlineVec {
    /// Storage!
    buf: [u8; LIMIT],
    /// Invariant: After masking off the tag, never exceeds LIMIT.
    tagged_len: u8,
}

impl InlineVec {
    #[inline]
    pub const fn new() -> Self {
        // Safety: Trivially, 0 <= LIMIT
        unsafe { Self::from_buf([0; LIMIT], 0) }
    }

    #[inline]
    pub const fn from_slice(bytes: &[u8]) -> Result<Self, ()> {
        let len = bytes.len();
        if len > LIMIT {
            return Err(());
        }

        let mut buf = [0; LIMIT];
        let mut i = 0;
        while i < len {
            buf[i] = bytes[i];
            i += 1;
        }

        // Safety: If len > LIMIT, Err was returned earlier.
        unsafe { Ok(Self::from_buf(buf, len)) }
    }

    /// The given length may not exceed LIMIT.
    #[inline]
    pub const unsafe fn from_buf(buf: [u8; LIMIT], len: usize) -> Self {
        debug_assert!(len <= LIMIT);
        Self { buf, tagged_len: len as u8 | LEN_TAG }
    }

    #[inline]
    pub fn len(&self) -> usize {
        usize::from(self.tagged_len & LEN_MASK)
    }

    /// The given length may not exceed LIMIT.
    #[inline]
    unsafe fn set_len(&mut self, len: usize) {
        debug_assert!(len <= LIMIT);
        self.tagged_len = len as u8 | LEN_TAG;
    }

    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        // Safety: We have the invariant `len <= LIMIT`.
        unsafe { self.buf.get_unchecked(..self.len()) }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        // Safety: We have the invariant `len <= LIMIT`.
        let len = self.len();
        unsafe { self.buf.get_unchecked_mut(..len) }
    }

    #[inline]
    pub fn clear(&mut self) {
        unsafe {
            // Safety: Trivially, `0 <= LIMIT`.
            self.set_len(0);
        }
    }

    #[inline]
    pub fn push(&mut self, byte: u8) -> Result<(), ()> {
        let len = self.len();
        if let Some(slot) = self.buf.get_mut(len) {
            *slot = byte;
            unsafe {
                // Safety: The `get_mut` call guarantees that `len < LIMIT`.
                self.set_len(len + 1);
            }
            Ok(())
        } else {
            Err(())
        }
    }

    #[inline]
    pub fn pop(&mut self) -> Option<u8> {
        let len = self.len();
        let byte = self.as_slice().last().copied()?;
        unsafe {
            // Safety: Finding a last element guarantees that `len > 0`, so the
            // new length is in bounds.
            self.set_len(len - 1);
        }
        Some(byte)
    }

    #[inline]
    pub fn insert(&mut self, index: usize, byte: u8) -> Result<(), ()> {
        let len = self.len();
        if index > len {
            out_of_bounds(index, len);
        }
        if len >= LIMIT {
            return Err(());
        }

        let ptr = self.buf.as_mut_ptr();
        unsafe {
            // Safety:
            // - `index <= len < LIMIT`, as checked above.
            // - The source is valid for `len - index` reads.
            // - The destination is valid for `len - index` writes because the
            //   inline buffer has at least one free byte.
            let at = ptr.add(index);
            ptr::copy(at, at.add(1), len - index);
            ptr::write(at, byte);

            // Safety: `len < LIMIT`, as checked above.
            self.set_len(len + 1);
        }
        Ok(())
    }

    #[inline]
    pub fn remove(&mut self, index: usize) -> u8 {
        let len = self.len();
        if index >= len {
            out_of_bounds(index, len);
        }

        let ptr = self.buf.as_mut_ptr();
        unsafe {
            // Safety: `index < len`, so this byte is initialized.
            let at = ptr.add(index);
            let byte = ptr::read(at);

            // Safety:
            // - The source is valid for `len - index - 1` reads.
            // - The destination is valid for the same number of writes.
            ptr::copy(at.add(1), at, len - index - 1);

            // Safety: `index < len` guarantees `len > 0`.
            self.set_len(len - 1);
            byte
        }
    }

    #[inline]
    pub fn extend_from_slice(&mut self, bytes: &[u8]) -> Result<(), ()> {
        let len = self.len();
        let Some(grown) = len.checked_add(bytes.len()) else { return Err(()) };
        if let Some(segment) = self.buf.get_mut(len..grown) {
            segment.copy_from_slice(bytes);
            unsafe {
                // Safety: The `get_mut` call guarantees that `grown <= LIMIT`.
                self.set_len(grown);
            }
            Ok(())
        } else {
            Err(())
        }
    }

    #[inline]
    pub fn insert_slice(&mut self, index: usize, bytes: &[u8]) -> Result<(), ()> {
        let len = self.len();
        assert!(index <= len, "index {index} out of range for slice of length {len}");

        let Some(grown) = len.checked_add(bytes.len()) else { return Err(()) };
        let tail_len = len - index;
        if grown <= LIMIT {
            let ptr = self.buf.as_mut_ptr();
            unsafe {
                // Safety: Checked that `index <= len` and
                // `len + bytes.len() == grown <= LIMIT`.
                ptr::copy(ptr.add(index), ptr.add(index + bytes.len()), tail_len);

                // Safety: Checked that `index <= len` and
                // `len + bytes.len() == grown <= LIMIT`.
                ptr::copy_nonoverlapping(bytes.as_ptr(), ptr.add(index), bytes.len());

                // Safety: Checked that `grown <= LIMIT`.
                self.set_len(grown);
            }
            Ok(())
        } else {
            Err(())
        }
    }

    #[inline]
    pub fn truncate(&mut self, target: usize) {
        if target < self.len() {
            unsafe {
                // Safety: Checked that it's smaller than the current length,
                // which cannot exceed LIMIT itself.
                self.set_len(target);
            }
        }
    }

    #[inline]
    pub fn remove_range<R>(&mut self, range: R)
    where
        R: RangeBounds<usize>,
    {
        let len = self.len();
        let range = crate::vendor::slice::range(range, ..len);

        let tail_len = len - range.end;
        let target = len - range.len();
        let ptr = self.buf.as_mut_ptr();
        unsafe {
            // Safety: The range is in bounds
            ptr::copy(ptr.add(range.end), ptr.add(range.start), tail_len);

            // Safety: Checked that it's smaller than the current length,
            // which cannot exceed LIMIT itself.
            self.set_len(target);
        }
    }
}

#[cold]
const fn exceeded_inline_capacity() -> ! {
    panic!("exceeded inline capacity");
}

#[cold]
fn out_of_bounds(index: usize, len: usize) -> ! {
    panic!("index is out bounds (index: {index}, len: {len})");
}

#[cfg(feature = "std")]
impl std::io::Write for EcoBytes {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.extend_from_slice(buf);
        Ok(buf.len())
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

#[cfg(feature = "serde")]
mod serde {
    use super::EcoBytes;
    use core::fmt;
    use serde::de::{Deserializer, SeqAccess, Visitor};

    impl serde::Serialize for EcoBytes {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            serializer.serialize_bytes(self.as_slice())
        }
    }

    struct EcoBytesVisitor;

    impl<'de> Visitor<'de> for EcoBytesVisitor {
        type Value = EcoBytes;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a byte buffer")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let mut bytes = EcoBytes::with_capacity(seq.size_hint().unwrap_or(0));
            while let Some(byte) = seq.next_element()? {
                bytes.push(byte);
            }
            Ok(bytes)
        }

        fn visit_bytes<E>(self, bytes: &[u8]) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            Ok(EcoBytes::from(bytes))
        }

        fn visit_str<E>(self, string: &str) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            self.visit_bytes(string.as_bytes())
        }
    }

    impl<'de> serde::Deserialize<'de> for EcoBytes {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_bytes(EcoBytesVisitor)
        }
    }
}
