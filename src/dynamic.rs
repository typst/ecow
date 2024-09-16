use core::mem::{self, ManuallyDrop};
use core::ptr;

use super::EcoVec;

/// A byte vector that can hold up to 15 bytes inline and then spills to an
/// `EcoVec<u8>`.
pub(crate) struct DynamicVec(Repr);

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

impl DynamicVec {
    #[inline]
    pub const fn new() -> Self {
        Self::from_inline(InlineVec::new())
    }

    #[inline]
    pub const fn from_inline(inline: InlineVec) -> Self {
        Self(Repr { inline })
    }

    #[inline]
    pub const fn from_eco(vec: EcoVec<u8>) -> Self {
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

    #[inline]
    pub fn from_slice(bytes: &[u8]) -> Self {
        match InlineVec::from_slice(bytes) {
            Ok(inline) => Self::from_inline(inline),
            _ => Self::from_eco(EcoVec::from(bytes)),
        }
    }

    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        if capacity <= LIMIT {
            Self::new()
        } else {
            Self::from_eco(EcoVec::with_capacity(capacity))
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        match self.variant() {
            Variant::Inline(inline) => inline.len(),
            Variant::Spilled(spilled) => spilled.len(),
        }
    }

    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        match self.variant() {
            Variant::Inline(inline) => inline.as_slice(),
            Variant::Spilled(spilled) => spilled.as_slice(),
        }
    }

    #[inline]
    pub fn make_mut(&mut self) -> &mut [u8] {
        match self.variant_mut() {
            VariantMut::Inline(inline) => inline.as_mut_slice(),
            VariantMut::Spilled(spilled) => spilled.make_mut(),
        }
    }

    #[inline]
    pub fn push(&mut self, byte: u8) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => {
                if inline.push(byte).is_err() {
                    let mut eco = EcoVec::with_capacity(LIMIT * 2);
                    eco.extend_from_byte_slice(self.as_slice());
                    eco.push(byte);
                    *self = Self::from_eco(eco);
                }
            }
            VariantMut::Spilled(spilled) => {
                spilled.push(byte);
            }
        }
    }

    #[inline]
    pub fn extend_from_slice(&mut self, bytes: &[u8]) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => {
                if inline.extend_from_slice(bytes).is_err() {
                    let needed = inline.len() + bytes.len();
                    let mut eco = EcoVec::with_capacity(needed.next_power_of_two());
                    eco.extend_from_byte_slice(self.as_slice());
                    eco.extend_from_byte_slice(bytes);
                    *self = Self::from_eco(eco);
                }
            }
            VariantMut::Spilled(spilled) => {
                spilled.extend_from_byte_slice(bytes);
            }
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => inline.clear(),
            VariantMut::Spilled(spilled) => spilled.clear(),
        }
    }

    #[inline]
    pub fn truncate(&mut self, target: usize) {
        match self.variant_mut() {
            VariantMut::Inline(inline) => inline.truncate(target),
            VariantMut::Spilled(spilled) => spilled.truncate(target),
        }
    }
}

impl DynamicVec {
    // If this returns true, guarantees that `self.0.inline` is initialized.
    // Otherwise, guarantees that `self.0.spilled` is initialized.
    #[inline]
    fn is_inline(&self) -> bool {
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

impl Clone for DynamicVec {
    #[inline]
    fn clone(&self) -> Self {
        match self.variant() {
            Variant::Inline(inline) => Self::from_inline(*inline),
            Variant::Spilled(spilled) => Self::from_eco(spilled.clone()),
        }
    }
}

impl Drop for DynamicVec {
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
