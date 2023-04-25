//! A clone-on-write, small-vector-optimized alternative to
//! [`Vec<u8>`][alloc::vec::Vec].

use core::mem::{self, ManuallyDrop};
use core::ops::Deref;
use core::ptr;

use super::EcoVec;

/// An economical byte vector with inline storage and clone-on-write semantics.
///
/// This type has a size of 16 bytes. It has 15 bytes of inline storage and
/// starting from 16 bytes it becomes an [`EcoVec<u8>`](super::EcoVec). The
/// internal reference counter of the heap variant is atomic, making this type
/// [`Sync`] and [`Send`].
///
///
/// # Note
/// The above holds true for normal 32-bit or 64-bit little endian systems. On
/// 64-bit big-endian systems, the type's size increases to 24 bytes and the
/// amount of inline storage to 23 bytes.
pub struct EcoBytes(Repr);

/// The internal representation.
///
/// On 64-bit little endian, this assumes that no valid EcoVec exists in which
/// the highest-order bit of the InlineVec's `tagged_len` would be set. This is
/// true because EcoVec is repr(C) and it's second field `len` is bounded by
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
///   inline variants doesn't overlap with the EcoVec. For little endian, its
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
    /// Maximum number of bytes for an inline `EcoBytes` before spilling on
    /// the heap.
    ///
    /// The exact value for this is architecture dependent.
    ///
    /// # Note
    /// This value is semver exempt and can be changed with any update.
    pub const INLINE_LIMIT: usize = LIMIT;

    /// Create a new, empty vector.
    #[inline]
    pub const fn new() -> Self {
        Self::from_inline(InlineVec::new())
    }

    /// Create a new, inline vector.
    ///
    /// Panics if the vector's length exceeds the capacity of the inline
    /// storage.
    #[inline]
    pub const fn inline(bytes: &[u8]) -> Self {
        let Ok(inline) = InlineVec::from_slice(bytes) else {
            exceeded_inline_capacity();
        };
        EcoBytes::from_inline(inline)
    }

    /// Create a new, inline vector.
    ///
    /// Returns `Err(())` if the vector's length exceeds the capacity of
    /// the inline storage.
    #[inline]
    pub const fn try_inline(bytes: &[u8]) -> Result<Self, ()> {
        match InlineVec::from_slice(bytes) {
            Ok(inline) => Ok(EcoBytes::from_inline(inline)),
            _ => Err(()),
        }
    }

    #[inline]
    pub(crate) const fn from_inline(inline: InlineVec) -> Self {
        Self(Repr { inline })
    }

    /// Create an instance from a slice.
    #[inline]
    pub fn from_slice(bytes: &[u8]) -> Self {
        match InlineVec::from_slice(bytes) {
            Ok(inline) => Self::from_inline(inline),
            _ => Self::from(EcoVec::from(bytes)),
        }
    }

    /// Create an empty vector with the given capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        if capacity <= LIMIT {
            Self::new()
        } else {
            Self::from(EcoVec::with_capacity(capacity))
        }
    }

    /// Returns `true` if the vector contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The length of the vector.
    #[inline]
    pub fn len(&self) -> usize {
        match self.variant() {
            Variant::Inline(inline) => inline.len(),
            Variant::Spilled(spilled) => spilled.len(),
        }
    }

    /// How many bytes this vector's backing allocation can hold.
    ///
    /// Even if `len < capacity`, pushing into the vector may still allocate if the reference count is larger than one.
    #[inline]
    pub fn capacity(&self) -> usize {
        match self.variant() {
            Variant::Inline(_) => Self::INLINE_LIMIT,
            Variant::Spilled(spilled) => spilled.capacity(),
        }
    }

    /// A slice containing the entire vector.
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        match self.variant() {
            Variant::Inline(inline) => inline.as_slice(),
            Variant::Spilled(spilled) => spilled.as_slice(),
        }
    }

    /// Produce a mutable slice containing the entire vector.
    ///
    /// Clones the vector if its reference count is larger than 1.
    pub fn make_mut(&mut self) -> &mut [u8] {
        match self.variant_mut() {
            VariantMut::Inline(inline) => inline.as_slice_mut(),
            VariantMut::Spilled(_) => todo!(),
        }
    }

    /// Add a byte at the end of the vector.
    ///
    /// Clones the vector if its reference count is larger than 1.
    #[inline]
    pub fn push(&mut self, byte: u8) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => {
                if inline.push(byte).is_err() {
                    let mut eco = EcoVec::with_capacity(inline.len() + 1);
                    eco.extend_from_byte_slice(self.as_slice());
                    eco.push(byte);
                    *self = Self::from(eco);
                }
            }
            VariantMut::Spilled(spilled) => {
                spilled.push(byte);
            }
        }
    }

    /// Removes the last byte from a vector and returns it, or `None` if the
    /// vector is empty.
    ///
    /// Clones the vector if its reference count is larger than 1.
    #[inline]
    pub fn pop(&mut self) -> Option<u8> {
        match self.variant_mut() {
            VariantMut::Inline(inline) => inline.pop(),
            VariantMut::Spilled(spilled) => spilled.pop(),
        }
    }

    /// Clear the vector.
    #[inline]
    pub fn clear(&mut self) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => inline.clear(),
            VariantMut::Spilled(spilled) => spilled.clear(),
        }
    }

    /// Shortens the vector, keeping the first len elements and dropping the
    /// rest.
    ///
    /// Clones the vector if its reference count is larger than 1 and
    /// `target < len`.
    #[inline]
    pub fn truncate(&mut self, target: usize) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => inline.truncate(target),
            VariantMut::Spilled(spilled) => spilled.truncate(target),
        }
    }

    /// Reserve space for at least `additional` more elements
    ///
    /// Guarantees that the resulting vector has reference count `1` and space for `additional` more elements
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => {
                if inline.len() + additional > LIMIT {
                    //TODO: optimize
                    let inline = *inline;
                    *self = Self::with_capacity(inline.len() + additional);
                    self.extend_from_slice(inline.as_slice())
                }
            }
            VariantMut::Spilled(spilled) => spilled.reserve(additional),
        }
    }

    /// Clones and pushes all elements in a slice to the vector.
    #[inline]
    pub fn extend_from_slice(&mut self, bytes: &[u8]) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => {
                if inline.extend_from_slice(bytes).is_err() {
                    let mut eco = EcoVec::with_capacity(inline.len() + bytes.len());
                    eco.extend_from_byte_slice(self.as_slice());
                    eco.extend_from_byte_slice(bytes);
                    *self = Self::from(eco);
                }
            }
            VariantMut::Spilled(spilled) => {
                spilled.extend_from_byte_slice(bytes);
            }
        }
    }

    /// Check whether this byte vector is stored inline
    // If this returns true, guarantees that `self.0.inline` is initialized.
    // Otherwise, guarantees that `self.0.spilled` is initialized.
    #[inline]
    pub fn is_inline(&self) -> bool {
        // Safety:
        // We always initialize tagged_len, even for the `EcoVec` variant. For
        // the inline variant the highest-order bit is always `1`. For the
        // spilled variant, it is initialized with `0` and cannot deviate from
        // that because the EcoVec's `len` field is bounded by `isize::MAX`. (At
        // least one 64-bit little endian; on 32-bit or big-endian the EcoVec
        // and tagged_len fields don't even overlap, meaning tagged_len stays at
        // its initial value.)
        unsafe { self.0.inline.tagged_len & LEN_TAG != 0 }
    }
}

impl Deref for EcoBytes {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl EcoBytes {
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
            Variant::Spilled(spilled) => Self::from(spilled.clone()),
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

impl From<EcoVec<u8>> for EcoBytes {
    #[inline]
    fn from(value: EcoVec<u8>) -> Self {
        // Safety:
        // Explicitly set `tagged_len` to 0 to mark this as a spilled variant.
        // Just initializing with `Repr { spilled: ... }` would leave
        // `tagged_len` unitialized, leading to undefined behaviour on access.
        let mut repr = Repr {
            inline: InlineVec { buf: [0; LIMIT], tagged_len: 0 },
        };
        repr.spilled = ManuallyDrop::new(value);
        Self(repr)
    }
}

impl From<EcoBytes> for EcoVec<u8> {
    #[inline]
    fn from(mut value: EcoBytes) -> Self {
        match value.variant_mut() {
            VariantMut::Inline(inline) => EcoVec::from(inline.as_slice()),
            VariantMut::Spilled(spilled) => {
                let mut ret = EcoVec::default();
                core::mem::swap(spilled, &mut ret);
                core::mem::forget(value);
                ret
            }
        }
    }
}

impl From<&'_ [u8]> for EcoBytes {
    #[inline]
    fn from(value: &'_ [u8]) -> Self {
        Self::from_slice(value)
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
        Self::from_buf([0; LIMIT], 0)
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

        Ok(Self::from_buf(buf, len))
    }

    #[inline]
    pub const fn from_buf(buf: [u8; LIMIT], len: usize) -> Self {
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
    pub fn as_slice_mut(&mut self) -> &mut [u8] {
        let len = self.len();
        // Safety: We have the invariant `len <= LIMIT`.
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
        let last = self.as_slice().last().copied();
        let len = self.len().saturating_sub(1);
        unsafe {
            // Safety: self.len().saturating_sub(1) <= self.len()
            self.set_len(len);
        }
        last
    }

    #[inline]
    pub fn extend_from_slice(&mut self, bytes: &[u8]) -> Result<(), ()> {
        let len = self.len();
        let grown = len + bytes.len();
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
    pub fn truncate(&mut self, target: usize) {
        if target < self.len() {
            unsafe {
                // Safety: Checked that it's smaller than the current length,
                // which cannot exceed LIMIT itself.
                self.set_len(target);
            }
        }
    }
}

#[cold]
const fn exceeded_inline_capacity() -> ! {
    panic!("exceeded inline capacity");
}
