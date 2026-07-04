//! An economical map with inline storage and clone-on-write semantics.

use core::{
    borrow::Borrow,
    fmt,
    hash::{BuildHasher, Hash},
    iter::FusedIterator,
    mem::{ManuallyDrop, MaybeUninit},
    ops::Index,
};

use crate::EcoVec;

#[cfg(not(feature = "sync"))]
use alloc::rc::Rc as SharedPtr;

#[cfg(feature = "sync")]
use alloc::sync::Arc as SharedPtr;

#[cfg(feature = "std")]
use std::{
    collections::{hash_map, HashMap, TryReserveError},
    hash::RandomState as DefaultHashBuilder,
};

#[cfg(not(feature = "std"))]
use hashbrown::{hash_map, DefaultHashBuilder, HashMap, TryReserveError};

// Type definitions and invariants.

/// An economical map with inline storage and clone-on-write semantics.
///
/// Inline invariants:
/// - `N` is in `1..=32` so every inline slot can be represented in `mask`.
/// - `mask` has exactly `len` bits set.
/// - Each set mask bit corresponds to an initialized slot.
/// - Each unset mask bit corresponds to an uninitialized slot.
/// - Linear probing remains valid from `bucket(key)` until the first empty slot.
///
/// Spilled invariants:
/// - Entries live in an `Rc<HashMap<K, V, S>>`.
/// - Mutating spilled maps uses `Rc::make_mut`, so mutating APIs require clone bounds.
pub enum EcoMap<K, V, const N: usize = 8, S = DefaultHashBuilder> {
    /// Inline storage: the map's entries are stored directly in the enum without heap allocation.
    Inline {
        /// The hasher used for key hashing.
        hash_builder: S,
        /// Has exactly `len` bits set, each set bit corresponding to an initialized slot.
        mask: u32,
        /// Fixed-size array of `N` slots, where only slots whose bit is set in `mask` are initialized.
        slots: [MaybeUninit<(K, V)>; N],
    },
    /// Heap-allocated storage: the map has spilled to the heap and is stored in a reference-counted `HashMap`.
    ///
    /// Mutation uses `Rc::make_mut` / `Arc::make_mut`, so clone bounds are required for mutating APIs.
    Spilled(SharedPtr<HashMap<K, V, S>>),
}

/// Result of probing the inline linear-probing table.
enum ProbeResult<T> {
    /// The closure matched and returned a value early.
    Found(T),
    /// Hit an empty slot at this specific index.
    HitEmpty(usize),
    /// Probed all N slots and they were all occupied by other keys.
    Full,
}

// Default-hasher constructors.

impl<K, V, const N: usize, S> EcoMap<K, V, N, S>
where
    S: Default,
{
    /// Creates an empty `EcoMap`.
    ///
    /// The hash map is initially created inline, so it will not allocate until it spills to the heap.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// let map: EcoMap<&str, i32> = EcoMap::new();
    /// assert_eq!(map.len(), 0);
    /// assert_eq!(map.capacity(), 8);
    /// ```
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an empty `EcoMap` with at least the specified capacity.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating.
    /// If `capacity` is less than or equal to `N`, the hash map will not allocate.
    /// Otherwise, the hash map will immediately spill to the heap and use a regular `HashMap`.
    /// As such, using this function is probably unnecessary and `new` is probably preferred.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// let mut map: EcoMap<&str, i32> = EcoMap::with_capacity(10);
    /// ```
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, S::default())
    }
}

// Core helpers, custom-hasher constructors, and basic accessors.

impl<K, V, const N: usize, S> EcoMap<K, V, N, S> {
    const _VALIDATE_CAPACITY: () = {
        assert!(N <= 32, "EcoMap inline capacity N cannot exceed 32 elements!");
        assert!(N > 0, "EcoMap inline capacity N must be greater than 0!");
    };

    // Inline storage helpers.

    #[inline(always)]
    fn slot_is_init(mask: u32, idx: usize) -> bool {
        (mask & (1 << idx)) != 0
    }

    #[inline(always)]
    unsafe fn slot_ref_unchecked(
        slots: &[MaybeUninit<(K, V)>; N],
        idx: usize,
    ) -> (&K, &V) {
        // SAFETY: The caller guarantees that `idx` is in bounds and initialized.
        let (k, v) = unsafe { slots.get_unchecked(idx).assume_init_ref() };
        (k, v)
    }

    #[inline(always)]
    unsafe fn slot_mut_unchecked(
        slots: &mut [MaybeUninit<(K, V)>; N],
        idx: usize,
    ) -> (&mut K, &mut V) {
        // SAFETY: The caller guarantees that `idx` is in bounds and initialized.
        let (k, v) = unsafe { slots.get_unchecked_mut(idx).assume_init_mut() };
        (k, v)
    }

    #[inline(always)]
    unsafe fn slot_read_unchecked(
        slots: &[MaybeUninit<(K, V)>; N],
        idx: usize,
    ) -> (K, V) {
        // SAFETY: The caller guarantees that `idx` is in bounds and initialized.
        unsafe { slots.get_unchecked(idx).assume_init_read() }
    }

    #[inline(always)]
    unsafe fn slot_write_unchecked(
        slots: &mut [MaybeUninit<(K, V)>; N],
        idx: usize,
        value: (K, V),
    ) {
        // SAFETY: The caller guarantees that `idx` is in bounds and uninitialized.
        unsafe { slots.get_unchecked_mut(idx).write(value) };
    }

    #[inline(always)]
    unsafe fn slot_move_unchecked(
        slots: &mut [MaybeUninit<(K, V)>; N],
        from: usize,
        to: usize,
    ) {
        // SAFETY: The caller guarantees that `from` is initialized and `to` is in bounds.
        // Replacing `from` with uninit moves the initialized value into `to`.
        unsafe {
            let source_slot = slots.get_unchecked_mut(from);
            *slots.get_unchecked_mut(to) =
                core::mem::replace(source_slot, MaybeUninit::uninit());
        }
    }

    #[inline(always)]
    fn slot_ref(
        slots: &[MaybeUninit<(K, V)>; N],
        mask: u32,
        idx: usize,
    ) -> Option<(&K, &V)> {
        if Self::slot_is_init(mask, idx) {
            // SAFETY: The mask bit guarantees this slot is initialized.
            Some(unsafe { Self::slot_ref_unchecked(slots, idx) })
        } else {
            None
        }
    }

    #[inline(always)]
    fn probe_index<Q>(
        slots: &[MaybeUninit<(K, V)>; N],
        mask: u32,
        start_idx: usize,
        key: &Q,
    ) -> ProbeResult<usize>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        for i in 0..N {
            let idx = (start_idx + i) % N;

            match Self::slot_ref(slots, mask, idx) {
                Some((k, _)) => {
                    if k.borrow() == key {
                        return ProbeResult::Found(idx);
                    }
                }
                None => return ProbeResult::HitEmpty(idx),
            }
        }
        ProbeResult::Full
    }

    // Custom-hasher constructors.

    /// Creates an empty `EcoMap` which will use the given hash builder to hash
    /// keys.
    ///
    /// The created map has the default initial capacity.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and
    /// is designed to allow HashMaps to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for
    /// the `EcoMap` to be useful, see its documentation for details.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::hash::RandomState;
    /// use ecow::EcoMap;
    ///
    /// let s = RandomState::new();
    /// let mut map = EcoMap::<_, _>::with_hasher(s);
    /// map.insert(1, 2);
    /// ```
    #[inline]
    #[must_use]
    pub const fn with_hasher(hash_builder: S) -> Self {
        let _ = Self::_VALIDATE_CAPACITY;

        Self::Inline {
            hash_builder,
            mask: 0,
            slots: [const { MaybeUninit::uninit() }; _],
        }
    }

    /// Creates an empty `EcoMap` with at least the specified capacity, using
    /// `hasher` to hash the keys.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating.
    /// If `capacity` is less than or equal to `N`, the hash map will not allocate.
    /// Otherwise, the hash map will immediately spill to the heap and use a regular `HashMap`.
    /// As such, using this function is probably unnecessary and `with_hasher` is probably preferred.
    ///
    /// Warning: `hasher` is normally randomly generated, and
    /// is designed to allow HashMaps to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    ///
    /// The `hasher` passed should implement the [`BuildHasher`] trait for
    /// the `EcoMap` to be useful, see its documentation for details.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::hash::RandomState;
    /// use ecow::EcoMap;
    ///
    /// let s = RandomState::new();
    /// let mut map = EcoMap::<_, _>::with_capacity_and_hasher(10, s);
    /// map.insert(1, 2);
    /// ```
    #[inline]
    #[must_use]
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        if capacity <= N {
            Self::with_hasher(hash_builder)
        } else {
            Self::Spilled(SharedPtr::new(HashMap::with_capacity_and_hasher(
                capacity,
                hash_builder,
            )))
        }
    }

    // Basic accessors.

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the `EcoMap<K, V>` might be able to hold
    /// more, but is guaranteed to be able to hold at least this many.
    ///
    /// When the map is still inline, its capacity will always be `N`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// let map: EcoMap<&str, i32> = EcoMap::new();
    /// assert_eq!(map.len(), 0);
    /// assert_eq!(map.capacity(), 8);

    /// let map: EcoMap<i32, i32> = EcoMap::with_capacity(100);
    /// assert_eq!(map.len(), 0);
    /// assert!(map.capacity() >= 100);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        match self {
            EcoMap::Inline { .. } => N,
            EcoMap::Spilled(spilled) => spilled.capacity(),
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// The iterator element type is `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// let mut count = 0;
    ///
    /// for (_key, _val) in map.iter() {
    ///     count += 1;
    /// }
    ///
    /// assert_eq!(count, 3);
    /// ```
    #[inline]
    pub fn iter(&self) -> EcoIter<'_, K, V, N> {
        match self {
            Self::Inline { slots, mask, .. } => EcoIter::Inline { slots, mask: *mask },
            Self::Spilled(spilled) => EcoIter::Spilled(spilled.iter()),
        }
    }

    /// Converts `self` into a parallel iterator.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// // This doctest is ignored under Miri because rayon's dependency
    /// // `crossbeam-epoch` uses integer-to-pointer casts internally,
    /// // which Miri's strict provenance checks flag as a false positive.
    /// // The issue is upstream in crossbeam, not in this crate.
    /// use ecow::EcoMap;
    /// use rayon::prelude::*;
    ///
    /// let mut map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("cc", 3),
    /// ]);
    ///
    /// map.par_iter().for_each(|(k, _)| println!("{k}"));
    /// assert_eq!(map.into_iter().collect::<Vec<_>>(), [("a", 1), ("b", 2), ("cc", 3)]);
    /// ```
    #[cfg(feature = "sync")]
    #[inline]
    pub fn par_iter(&self) -> impl rayon::iter::ParallelIterator<Item = (&K, &V)>
    where
        K: Eq + Hash + Sync,
        V: Sync,
        S: BuildHasher + Sync,
    {
        use rayon::iter::IntoParallelIterator;
        self.into_par_iter() // Calls IntoParallelIterator for &'a EcoMap
    }

    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for key in map.keys() {
    ///     println!("{key}");
    /// }
    /// ```
    #[inline]
    pub fn keys(&self) -> Keys<'_, K, V, N> {
        Keys { inner: self.iter() }
    }

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for val in map.values() {
    ///     println!("{val}");
    /// }
    /// ```
    #[inline]
    pub fn values(&self) -> Values<'_, K, V, N> {
        Values { inner: self.iter() }
    }

    /// Returns a reference to the map's [`BuildHasher`].
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// use std::hash::RandomState;
    ///
    /// let hasher = RandomState::new();
    /// let map: EcoMap<i32, i32> = EcoMap::with_hasher(hasher);
    /// let hasher: &RandomState = map.hasher();
    /// ```
    #[inline]
    pub fn hasher(&self) -> &S {
        match self {
            Self::Inline { hash_builder, .. } => hash_builder,
            Self::Spilled(spilled) => spilled.hasher(),
        }
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut a = EcoMap::<_, _>::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        match self {
            Self::Inline { mask, .. } => mask.count_ones() as _,
            Self::Spilled(spilled) => spilled.len(),
        }
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut a = EcoMap::<_, _>::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

// Hashing, spilling, and borrowed lookup.

impl<K, V, const N: usize, S> EcoMap<K, V, N, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    // Spilling helpers.

    fn spill_with_capacity(&mut self, capacity: usize) {
        let Self::Inline { .. } = self else {
            return;
        };

        // SAFETY: `self` is valid and initialized.
        let old_self = ManuallyDrop::new(unsafe { core::ptr::read(self) });
        let Self::Inline { hash_builder, mask, slots, .. } = &*old_self else {
            // SAFETY: We confirm above that `self` is inline.
            unsafe { core::hint::unreachable_unchecked() }
        };

        // SAFETY: `hash_builder` exists and is initialized.
        let hash_builder = unsafe { core::ptr::read(hash_builder) };
        let mut spilled =
            HashMap::<K, V, S>::with_capacity_and_hasher(capacity, hash_builder);

        let mut mask = *mask;
        while mask != 0 {
            let idx = mask.trailing_zeros() as usize;

            // SAFETY: The mask bit guarantees this slot is initialized.
            let (k, v) = unsafe { Self::slot_read_unchecked(slots, idx) };
            spilled.insert(k, v);
            mask &= mask - 1;
        }

        // SAFETY: `self` is valid.
        unsafe { core::ptr::write(self, Self::Spilled(SharedPtr::new(spilled))) };
    }

    /// Triggers an out-of-line memory allocation with 1.5x capacity scaling.
    ///
    /// Uses the bitwise growth factor `N + (N >> 1)` to eliminate floating-point
    /// overhead. This 1.5x stride allows memory allocators to eventually reuse
    /// previously freed memory blocks, reducing heap fragmentation compared to 2x doubling.
    #[inline]
    fn spill(&mut self) {
        let new_capacity = N + (N >> 1);
        self.spill_with_capacity(new_capacity);
    }

    // Hashing helper.

    /// Maps a key to a bucket index `[0, N[` using Lemire's Fast Range Reduction.
    ///
    /// ### Mathematical Mechanics
    /// Treats the 64-bit hash as a fraction `(Hash / 2^64)` in the range `[0, 1[`.
    /// Multiplying this fraction by the capacity `N` scales the range uniformly to `[0, N[`.
    /// Shifting right by 64 bits extracts the integer portion, bypassing slow hardware division.
    #[inline]
    fn bucket<Q>(key: &Q, hash_builder: &S) -> usize
    where
        Q: Hash + ?Sized,
    {
        let hash = hash_builder.hash_one(key);
        let capacity = N as u128;

        (((hash as u128) * capacity) >> 64) as _
    }

    // Unique mutation helpers.

    fn insert_unique(&mut self, key: K, value: V) -> Option<V> {
        match self {
            Self::Inline { hash_builder, slots, mask, .. } => {
                let start_idx = Self::bucket(&key, hash_builder);

                match Self::probe_index(slots, *mask, start_idx, &key) {
                    ProbeResult::Found(idx) => {
                        // SAFETY: `ProbeResult::Found` guarantees this slot is initialized.
                        let (_, v) = unsafe { Self::slot_mut_unchecked(slots, idx) };
                        Some(core::mem::replace(v, value))
                    }
                    ProbeResult::HitEmpty(idx) => {
                        // SAFETY: `ProbeResult::HitEmpty` guarantees this slot is uninitialized.
                        unsafe { Self::slot_write_unchecked(slots, idx, (key, value)) };
                        *mask |= 1 << idx;
                        None
                    }
                    ProbeResult::Full => {
                        self.spill();
                        self.insert_unique(key, value)
                    }
                }
            }
            Self::Spilled(rc) => SharedPtr::get_mut(rc)
                .expect("unique insertion requires uniquely owned spilled storage")
                .insert(key, value),
        }
    }

    // Borrowed lookup.

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map = EcoMap::<_, _>::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self {
            Self::Inline { hash_builder, slots, mask, .. } => {
                if *mask == 0 {
                    return None;
                }

                let start_idx = Self::bucket(key, hash_builder);
                if let ProbeResult::Found(idx) =
                    Self::probe_index(slots, *mask, start_idx, key)
                {
                    // SAFETY: `ProbeResult::Found` guarantees this slot is initialized.
                    let (_, v) = unsafe { Self::slot_ref_unchecked(slots, idx) };

                    Some(v)
                } else {
                    None
                }
            }
            Self::Spilled(spilled) => spilled.get(key),
        }
    }

    /// Returns the key-value pair corresponding to the supplied key. This is
    /// potentially useful:
    /// - for key types where non-identical keys can be considered equal;
    /// - for getting the `&K` stored key value from a borrowed `&Q` lookup key; or
    /// - for getting a reference to a key with the same lifetime as the collection.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// use std::hash::{Hash, Hasher};
    ///
    /// #[derive(Clone, Copy, Debug)]
    /// struct S {
    ///     id: u32,
    /// #   #[allow(unused)] // prevents a "field `name` is never read" error
    ///     name: &'static str, // ignored by equality and hashing operations
    /// }
    ///
    /// impl PartialEq for S {
    ///     fn eq(&self, other: &S) -> bool {
    ///         self.id == other.id
    ///     }
    /// }
    ///
    /// impl Eq for S {}
    ///
    /// impl Hash for S {
    ///     fn hash<H: Hasher>(&self, state: &mut H) {
    ///         self.id.hash(state);
    ///     }
    /// }
    ///
    /// let j_a = S { id: 1, name: "Jessica" };
    /// let j_b = S { id: 1, name: "Jess" };
    /// let p = S { id: 2, name: "Paul" };
    /// assert_eq!(j_a, j_b);
    ///
    /// let mut map = EcoMap::<_, _>::new();
    /// map.insert(j_a, "Paris");
    /// assert_eq!(map.get_key_value(&j_a), Some((&j_a, &"Paris")));
    /// assert_eq!(map.get_key_value(&j_b), Some((&j_a, &"Paris"))); // the notable case
    /// assert_eq!(map.get_key_value(&p), None);
    /// ```
    #[inline]
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self {
            Self::Inline { hash_builder, slots, mask, .. } => {
                if *mask == 0 {
                    return None;
                }

                let start_idx = Self::bucket(key, hash_builder);
                if let ProbeResult::Found(idx) =
                    Self::probe_index(slots, *mask, start_idx, key)
                {
                    // SAFETY: `ProbeResult::Found` guarantees this slot is initialized.
                    unsafe { Some(Self::slot_ref_unchecked(slots, idx)) }
                } else {
                    None
                }
            }
            Self::Spilled(spilled) => spilled.get_key_value(key),
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map = EcoMap::<_, _>::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    #[inline]
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self {
            Self::Inline { hash_builder, mask, slots } => {
                if *mask == 0 {
                    return false;
                }

                let start_idx = Self::bucket(key, hash_builder);
                matches!(
                    Self::probe_index(slots, *mask, start_idx, key),
                    ProbeResult::Found(_)
                )
            }
            Self::Spilled(spilled) => spilled.contains_key(key),
        }
    }
}

// Mutable access and mutation.

impl<K: Clone, V: Clone, const N: usize, S: Clone> EcoMap<K, V, N, S> {
    /// An iterator visiting all key-value pairs in arbitrary order,
    /// with mutable references to the values.
    /// The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// // Update all values
    /// for (_, val) in map.iter_mut() {
    ///     *val *= 2;
    /// }
    ///
    /// for (key, val) in &map {
    ///     println!("key: {key} val: {val}");
    /// }
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> EcoIterMut<'_, K, V, N> {
        match self {
            Self::Inline { slots, mask, .. } => EcoIterMut::Inline { slots, mask: *mask },
            Self::Spilled(rc) => {
                let spilled = SharedPtr::make_mut(rc);

                EcoIterMut::Spilled(spilled.iter_mut())
            }
        }
    }

    /// Converts `self` into a parallel iterator.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// // This doctest is ignored under Miri because rayon's dependency
    /// // `crossbeam-epoch` uses integer-to-pointer casts internally,
    /// // which Miri's strict provenance checks flag as a false positive.
    /// // The issue is upstream in crossbeam, not in this crate.
    /// use ecow::EcoMap;
    /// use rayon::prelude::*;
    ///
    /// let mut map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("cc", 3),
    /// ]);
    ///
    /// map.par_iter_mut().for_each(|(k, v)| *v = k.len());
    /// assert_eq!(map.into_iter().collect::<Vec<_>>(), [("a", 1), ("b", 1), ("cc", 2)]);
    /// ```
    #[cfg(feature = "sync")]
    #[inline]
    pub fn par_iter_mut(
        &mut self,
    ) -> impl rayon::iter::ParallelIterator<Item = (&K, &mut V)>
    where
        K: Send + Eq + Hash + Sync + Clone,
        V: Send + Clone,
        S: BuildHasher + Sync + Clone,
    {
        use rayon::iter::IntoParallelIterator;
        self.into_par_iter()
    }

    /// An iterator visiting all values mutably in arbitrary order.
    /// The iterator element type is `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for val in map.values_mut() {
    ///     *val = *val + 10;
    /// }
    ///
    /// for val in map.values() {
    ///     println!("{val}");
    /// }
    /// ```
    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V, N> {
        match self {
            Self::Inline { slots, mask, .. } => ValuesMut::Inline { slots, mask: *mask },
            Self::Spilled(rc) => {
                let spilled = SharedPtr::make_mut(rc);

                ValuesMut::Spilled(spilled.values_mut())
            }
        }
    }
}

impl<K, V, const N: usize, S> EcoMap<K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
    // Inlining helpers.

    fn inline(&mut self) {
        let Self::Spilled(spilled) = self else {
            return;
        };

        if spilled.len() > N {
            return;
        }

        if SharedPtr::strong_count(spilled) > 1 {
            return;
        }

        // SAFETY: `spilled`, which is `self`, is valid and initialized.
        let old_rc = unsafe { core::ptr::read(spilled) };
        let mut spilled = SharedPtr::into_inner(old_rc).unwrap();

        let hash_builder = spilled.hasher().clone();
        let mut inline = Self::with_hasher(hash_builder.clone());
        let Self::Inline { mask, slots, .. } = &mut inline else {
            // SAFETY: `EcoMap::with_hasher` gives us an inline map.
            unsafe { core::hint::unreachable_unchecked() }
        };

        for (k, v) in spilled.drain() {
            let start_idx = Self::bucket(&k, &hash_builder);
            let ProbeResult::HitEmpty(idx) =
                Self::probe_index(slots, *mask, start_idx, &k)
            else {
                // SAFETY: We just created this inline map. Every slot will be empty
                unsafe { core::hint::unreachable_unchecked() }
            };

            // SAFETY: `ProbeResult::HitEmpty` guarantees this slot is uninitialized.
            unsafe { Self::slot_write_unchecked(slots, idx, (k, v)) };
            *mask |= 1 << idx;
        }

        // SAFETY: `self` is valid.
        unsafe { core::ptr::write(self, inline) };
    }

    // Capacity management.

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `EcoMap`. The collection may reserve more space to speculatively
    /// avoid frequent reallocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    /// Also does nothing if map is inline and `self.len() + additional` is less than or equal to `N`.
    /// Otherwise, it will spill the map.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows [`usize`].
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// let mut map: EcoMap<&str, i32> = EcoMap::new();
    /// map.reserve(10);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        match self {
            EcoMap::Inline { mask, .. } => {
                let new = mask.count_ones() as usize + additional;
                if new > N {
                    self.spill_with_capacity(new);
                }
            }
            EcoMap::Spilled(rc) => {
                let spilled = SharedPtr::make_mut(rc);

                spilled.reserve(additional);
            }
        }
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// in the `EcoMap`. When the map is inline, this function does nothing if `self.len() + additional`
    /// is smaller than or equal to `N`. Otherwise, it spills the map.
    /// See `std::collections::HashMap::try_reserve` for more information.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map: EcoMap<&str, isize> = EcoMap::new();
    /// map.try_reserve(2); // No-op
    /// map.try_reserve(10); // Spills
    /// ```
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        match self {
            EcoMap::Inline { .. } => {
                let new = self.len() + additional;
                if new > N {
                    // Spilling instantiates a new `HashMap`, and as of now `HashMap` doesn't support `try_with_*` functions (such as `Vec` already does on `nightly`) and will just panic, as we do here.
                    // When it does our API should also mirror it.
                    self.spill_with_capacity(new);
                }
                Ok(())
            }
            EcoMap::Spilled(rc) => {
                let spilled = SharedPtr::make_mut(rc);

                spilled.try_reserve(additional)
            }
        }
    }

    /// Shrinks the capacity of the map as much as possible. This will inline the map again if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map: EcoMap<i32, i32, 4> = EcoMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() == 4);
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.shrink_to(0);
    }

    /// Shrinks the capacity of the map with a lower limit. This will inline the map again if possible.
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map: EcoMap<i32, i32, 4> = EcoMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10);
    /// map.shrink_to(0);
    /// assert!(map.capacity() == 4);
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        if let Self::Spilled(rc) = self {
            let spilled = SharedPtr::make_mut(rc);

            spilled.shrink_to(min_capacity);

            if min_capacity <= N && spilled.len() <= N && SharedPtr::strong_count(rc) == 1
            {
                self.inline();
            }
        }
    }
}

/// A draining iterator over the entries of a `EcoMap`.
///
/// This `struct` is created by the [`drain`] method on [`EcoMap`]. See its
/// documentation for more.
///
/// [`drain`]: EcoMap::drain
///
/// # Example
///
/// ```
/// use ecow::EcoMap;
///
/// let mut map = EcoMap::<_, _>::from([
///     ("a", 1),
/// ]);
/// let iter = map.drain();
/// ```
pub enum Drain<'a, K, V, const N: usize, S> {
    /// Drains entries from an inline `EcoMap`.
    Inline {
        /// A mutable reference to the inline `EcoMap` being drained.
        map: &'a mut EcoMap<K, V, N, S>,
    },
    /// Drains entries from a spilled `HashMap`.
    Spilled(hash_map::Drain<'a, K, V>),
}

impl<'a, K, V, const N: usize, S> Iterator for Drain<'a, K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Inline { map } => {
                let EcoMap::Inline { mask, slots, .. } = map else {
                    unsafe { core::hint::unreachable_unchecked() }
                };

                if *mask == 0 {
                    return None;
                }

                let idx = mask.trailing_zeros() as usize;
                *mask &= *mask - 1;

                // SAFETY: The mask bit guarantees this slot was initialized, and clearing it
                // prevents a double drop if dropping panics.
                Some(unsafe { EcoMap::<K, V, N>::slot_read_unchecked(slots, idx) })
            }
            Self::Spilled(drain) => drain.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }
}

impl<K, V, const N: usize, S> ExactSizeIterator for Drain<'_, K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
    #[inline]
    fn len(&self) -> usize {
        match self {
            Drain::Inline { map } => map.len(),
            Drain::Spilled(drain) => drain.len(),
        }
    }
}

impl<K, V, const N: usize, S> FusedIterator for Drain<'_, K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
}

impl<K, V, const N: usize, S> Drop for Drain<'_, K, V, N, S> {
    fn drop(&mut self) {
        if let Self::Inline { map } = self {
            if let EcoMap::Inline { mask, slots, .. } = map {
                while *mask != 0 {
                    let idx = mask.trailing_zeros() as usize;
                    *mask &= *mask - 1;

                    // SAFETY: The mask bit guarantees this slot is initialized, and
                    // clearing it first prevents a double drop if dropping panics.
                    unsafe { EcoMap::<K, V, N>::slot_read_unchecked(slots, idx) };
                }
            }
        }
    }
}

impl<K, V, const N: usize, S> EcoMap<K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
    /// Clears the map, returning all key-value pairs as an iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut a = EcoMap::<_, _>::new();
    /// a.insert(1, "a");
    /// a.insert(2, "b");
    ///
    /// for (k, v) in a.drain().take(1) {
    ///     assert!(k == 1 || k == 2);
    ///     assert!(v == "a" || v == "b");
    /// }
    ///
    /// assert!(a.is_empty());
    /// ```
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, K, V, N, S> {
        match self {
            Self::Inline { .. } => Drain::Inline { map: self },
            Self::Spilled(rc) => {
                let map = SharedPtr::make_mut(rc);
                Drain::Spilled(map.drain())
            }
        }
    }

    // Entry and mutable lookup.

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut letters = EcoMap::<_, _>::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     letters.entry(ch).and_modify(|counter| *counter += 1).or_insert(1);
    /// }
    ///
    /// assert_eq!(letters[&'s'], 2);
    /// assert_eq!(letters[&'t'], 3);
    /// assert_eq!(letters[&'u'], 1);
    /// assert_eq!(letters.get(&'y'), None);
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V, N, S> {
        if self.contains_key(&key) {
            Entry::Occupied(OccupiedEntry { map: self, key })
        } else {
            Entry::Vacant(VacantEntry { map: self, key })
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map = EcoMap::<_, _>::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self {
            Self::Inline { hash_builder, mask, slots } => {
                if *mask == 0 {
                    return None;
                }

                let start_idx = Self::bucket(key, hash_builder);

                if let ProbeResult::Found(idx) =
                    Self::probe_index(slots, *mask, start_idx, key)
                {
                    // SAFETY: `ProbeResult::Found` guarantees this slot is initialized.
                    let (_, v) = unsafe { Self::slot_mut_unchecked(slots, idx) };
                    Some(v)
                } else {
                    None
                }
            }
            Self::Spilled(rc) => {
                let spilled = SharedPtr::make_mut(rc);

                spilled.get_mut(key)
            }
        }
    }

    // Insertion and removal.

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, [`None`] is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the [`std::collections`]
    /// module-level documentation for more.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map = EcoMap::<_, _>::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self {
            Self::Inline { hash_builder, slots, mask } => {
                let start_idx = Self::bucket(&key, hash_builder);

                match Self::probe_index(slots, *mask, start_idx, &key) {
                    ProbeResult::Found(idx) => {
                        // SAFETY: `ProbeResult::Found` guarantees this slot is initialized.
                        let (_, v) = unsafe { Self::slot_mut_unchecked(slots, idx) };

                        Some(core::mem::replace(v, value))
                    }
                    ProbeResult::HitEmpty(idx) => {
                        // SAFETY: `ProbeResult::HitEmpty` guarantees this slot is uninitialized.
                        unsafe { Self::slot_write_unchecked(slots, idx, (key, value)) };
                        *mask |= 1 << idx;
                        None
                    }
                    ProbeResult::Full => {
                        self.spill();
                        self.insert(key, value)
                    }
                }
            }
            Self::Spilled(rc) => {
                let spilled = SharedPtr::make_mut(rc);

                spilled.insert(key, value)
            }
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` for which `f(&k, &mut v)` returns `false`.
    /// The elements are visited in unsorted (and unspecified) order.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map: EcoMap<i32, i32> = (0..8).map(|x| (x, x * 10)).collect();
    /// map.retain(|&k, _| k % 2 == 0);
    /// assert_eq!(map.len(), 4);
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        match self {
            Self::Inline { slots, mask, .. } => {
                let mut remove_keys = EcoVec::new();
                let mut active_mask = *mask;

                while active_mask != 0 {
                    let idx = active_mask.trailing_zeros() as usize;
                    active_mask &= active_mask - 1;

                    // SAFETY: The mask bit guarantees this slot is initialized.
                    let (key, value) = unsafe { Self::slot_mut_unchecked(slots, idx) };
                    if !f(key, value) {
                        remove_keys.push(key.clone());
                    }
                }

                for key in remove_keys {
                    self.remove(&key);
                }
            }
            Self::Spilled(rc) => {
                let spilled = SharedPtr::make_mut(rc);
                spilled.retain(f);
            }
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map = EcoMap::<_, _>::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    #[inline]
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.remove_entry(key).map(|(_, value)| value)
    }

    /// Removes a key from the map, returning the stored key and value if the
    /// key was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map = EcoMap::<_, _>::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove_entry(&1), Some((1, "a")));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self {
            Self::Inline { hash_builder, mask, slots } => {
                if *mask == 0 {
                    return None;
                }

                let start_idx = Self::bucket(key, hash_builder);

                let ProbeResult::Found(target_idx) =
                    Self::probe_index(slots, *mask, start_idx, key)
                else {
                    return None;
                };

                // SAFETY: `ProbeResult::Found` guarantees this slot is initialized.
                let removed_entry =
                    unsafe { Self::slot_read_unchecked(slots, target_idx) };

                *mask &= !(1 << target_idx);

                // Backward Shift
                let mut hole = target_idx;
                let mut scan = (target_idx + 1) % N;

                while (*mask & (1 << scan)) != 0 {
                    // SAFETY: The mask bit guarantees this slot is initialized.
                    let (scan_key, _) = unsafe { Self::slot_ref_unchecked(slots, scan) };
                    let ideal = Self::bucket(scan_key, hash_builder);

                    // Clockwise check: Is `ideal` strictly between `hole` and `scan`?
                    let ideal_is_trapped = if hole <= scan {
                        hole < ideal && ideal <= scan
                    } else {
                        hole < ideal || ideal <= scan
                    };

                    if !ideal_is_trapped {
                        // SAFETY: Both `hole` and `scan` are calculated via `% N`, so they are
                        // strictly within bounds of the array. The mask bit guarantees `scan` is initialized.
                        unsafe { Self::slot_move_unchecked(slots, scan, hole) };

                        *mask &= !(1 << scan);
                        *mask |= 1 << hole;

                        hole = scan;
                    }

                    scan = (scan + 1) % N;
                }

                Some(removed_entry)
            }
            Self::Spilled(rc) => {
                let spilled = SharedPtr::make_mut(rc);

                spilled.remove_entry(key)
            }
        }
    }

    /// Clears the map, removing all key-value pairs.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut a = EcoMap::<_, _>::new();
    /// a.insert(1, "a");
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        match self {
            EcoMap::Inline { mask, slots, .. } => {
                let mut active_mask = *mask;
                while active_mask != 0 {
                    let idx = active_mask.trailing_zeros() as usize;

                    // SAFETY: The mask bit guarantees this slot is initialized.
                    unsafe { Self::slot_read_unchecked(slots, idx) };
                    active_mask &= active_mask - 1;
                }
                *mask = 0;
            }
            EcoMap::Spilled(rc) => {
                let spilled = SharedPtr::make_mut(rc);

                spilled.clear();
            }
        }
    }
}

// Entry API.

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`] method on [`EcoMap`].
///
/// [`entry`]: EcoMap::entry
pub enum Entry<'a, K, V, const N: usize, S = DefaultHashBuilder> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V, N, S>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, K, V, N, S>),
}

/// A view into an occupied entry in a `EcoMap`.
/// It is part of the [`Entry`] enum.
pub struct OccupiedEntry<'a, K, V, const N: usize, S = DefaultHashBuilder> {
    map: &'a mut EcoMap<K, V, N, S>,
    key: K,
}

/// A view into a vacant entry in a `EcoMap`.
/// It is part of the [`Entry`] enum.
pub struct VacantEntry<'a, K, V, const N: usize, S = DefaultHashBuilder> {
    map: &'a mut EcoMap<K, V, N, S>,
    key: K,
}

impl<'a, K, V, const N: usize, S> Entry<'a, K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
    /// Returns a reference to this entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    #[inline]
    pub fn key(&self) -> &K {
        match self {
            Self::Occupied(entry) => entry.key(),
            Self::Vacant(entry) => entry.key(),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    ///
    /// map.entry("poneyland").or_insert(3);
    /// assert_eq!(map["poneyland"], 3);
    ///
    /// *map.entry("poneyland").or_insert(10) *= 2;
    /// assert_eq!(map["poneyland"], 6);
    /// ```
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Self::Occupied(entry) => entry.into_mut(),
            Self::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map = EcoMap::<_, _>::new();
    /// let value = "hoho";
    ///
    /// map.entry("poneyland").or_insert_with(|| value);
    ///
    /// assert_eq!(map["poneyland"], "hoho");
    /// ```
    #[inline]
    pub fn or_insert_with<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        match self {
            Self::Occupied(entry) => entry.into_mut(),
            Self::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows for generating key-derived values for insertion by providing the default
    /// function a reference to the key that was moved during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map: EcoMap<&str, usize> = EcoMap::new();
    ///
    /// map.entry("poneyland").or_insert_with_key(|key| key.chars().count());
    ///
    /// assert_eq!(map["poneyland"], 9);
    /// ```
    #[inline]
    pub fn or_insert_with_key<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce(&K) -> V,
    {
        match self {
            Self::Occupied(entry) => entry.into_mut(),
            Self::Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            }
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 42);
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 43);
    /// ```
    #[inline]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Self::Occupied(mut entry) => {
                f(entry.get_mut());
                Self::Occupied(entry)
            }
            Self::Vacant(entry) => Self::Vacant(entry),
        }
    }

    /// Sets the value of the entry, and returns an `OccupiedEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map: EcoMap<&str, String> = EcoMap::new();
    /// let entry = map.entry("poneyland").insert_entry("hoho".to_string());
    ///
    /// assert_eq!(entry.key(), &"poneyland");
    /// ```
    #[inline]
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, N, S> {
        match self {
            Self::Occupied(mut entry) => {
                entry.insert(value);
                entry
            }
            Self::Vacant(entry) => entry.insert_entry(value),
        }
    }
}

impl<'a, K, V, const N: usize, S> Entry<'a, K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone + Default,
    S: BuildHasher + Clone,
{
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map: EcoMap<&str, Option<u32>> = EcoMap::new();
    /// map.entry("poneyland").or_default();
    ///
    /// assert_eq!(map["poneyland"], None);
    /// ```
    #[inline]
    pub fn or_default(self) -> &'a mut V {
        self.or_insert_with(Default::default)
    }
}

impl<'a, K, V, const N: usize, S> OccupiedEntry<'a, K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
    /// Gets a reference to the key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    /// map.entry("poneyland").or_insert(12);
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    #[inline]
    pub fn key(&self) -> &K {
        self.map.get_key_value(&self.key).map(|(key, _)| key).unwrap()
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// use ecow::map::Entry;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.get(), &12);
    /// }
    /// ```
    #[inline]
    pub fn get(&self) -> &V {
        self.map.get(&self.key).unwrap()
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the `Entry` value, see [`into_mut`].
    ///
    /// [`into_mut`]: Self::into_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// use ecow::map::Entry;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     *o.get_mut() += 10;
    ///     assert_eq!(*o.get(), 22);
    ///
    ///     // We can use the same Entry multiple times.
    ///     *o.get_mut() += 2;
    /// }
    ///
    /// assert_eq!(map["poneyland"], 24);
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        self.map.get_mut(&self.key).unwrap()
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: Self::get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// use ecow::map::Entry;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     *o.into_mut() += 10;
    /// }
    ///
    /// assert_eq!(map["poneyland"], 22);
    /// ```
    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        self.map.get_mut(&self.key).unwrap()
    }

    /// Sets the value of the entry, and returns the entry's old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// use ecow::map::Entry;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     assert_eq!(o.insert(15), 12);
    /// }
    ///
    /// assert_eq!(map["poneyland"], 15);
    /// ```
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        core::mem::replace(self.get_mut(), value)
    }

    /// Takes the value out of the entry, and returns it.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// use ecow::map::Entry;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.remove(), 12);
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// ```
    #[inline]
    pub fn remove(self) -> V {
        self.map.remove(&self.key).unwrap()
    }

    /// Take the ownership of the key and value from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// use ecow::map::Entry;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     // We delete the entry from the map.
    ///     o.remove_entry();
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// ```
    #[inline]
    pub fn remove_entry(self) -> (K, V) {
        self.map.remove_entry(&self.key).unwrap()
    }
}

impl<'a, K, V, const N: usize, S> VacantEntry<'a, K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
    /// Gets a reference to the key that would be used when inserting a value
    /// through the `VacantEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    #[inline]
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Take ownership of the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// use ecow::map::Entry;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    ///
    /// if let Entry::Vacant(v) = map.entry("poneyland") {
    ///     v.into_key();
    /// }
    /// ```
    #[inline]
    pub fn into_key(self) -> K {
        self.key
    }

    /// Sets the value of the entry with the `VacantEntry`'s key,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// use ecow::map::Entry;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    ///
    /// if let Entry::Vacant(o) = map.entry("poneyland") {
    ///     o.insert(37);
    /// }
    /// assert_eq!(map["poneyland"], 37);
    /// ```
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        let key = self.key.clone();
        self.map.insert(self.key, value);
        self.map.get_mut(&key).unwrap()
    }

    /// Sets the value of the entry with the `VacantEntry`'s key,
    /// and returns an `OccupiedEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    /// use ecow::map::Entry;
    ///
    /// let mut map: EcoMap<&str, u32> = EcoMap::new();
    ///
    /// if let Entry::Vacant(o) = map.entry("poneyland") {
    ///     o.insert_entry(37);
    /// }
    /// assert_eq!(map["poneyland"], 37);
    /// ```
    #[inline]
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, N, S> {
        let key = self.key.clone();
        self.map.insert(self.key, value);
        OccupiedEntry { map: self.map, key }
    }
}

// Trait implementations.

impl<K, V, const N: usize, S> Default for EcoMap<K, V, N, S>
where
    S: Default,
{
    /// Creates an empty `EcoMap<K, V, S>`, with the `Default` value for the hasher.
    #[inline]
    fn default() -> Self {
        Self::with_hasher(Default::default())
    }
}

impl<K: Clone, V: Clone, const N: usize, S: Clone> Clone for EcoMap<K, V, N, S> {
    fn clone(&self) -> Self {
        match self {
            Self::Inline { hash_builder, mask, slots } => {
                let mut new_slots = [const { MaybeUninit::uninit() }; N];

                let mut new_mask = *mask;
                while new_mask != 0 {
                    let idx = new_mask.trailing_zeros() as usize;
                    new_mask &= new_mask - 1;

                    // SAFETY: The mask guarantees this slot is initialized.
                    let (k, v) = unsafe { Self::slot_ref_unchecked(slots, idx) };
                    // SAFETY: `new_slots` starts empty and each set mask bit is visited once.
                    unsafe {
                        Self::slot_write_unchecked(
                            &mut new_slots,
                            idx,
                            (k.clone(), v.clone()),
                        )
                    };
                }

                Self::Inline {
                    hash_builder: hash_builder.clone(),
                    mask: *mask,
                    slots: new_slots,
                }
            }
            Self::Spilled(spilled) => Self::Spilled(SharedPtr::clone(spilled)),
        }
    }
}

impl<'a, K, V, const N: usize, S> IntoIterator for &'a EcoMap<K, V, N, S> {
    type Item = (&'a K, &'a V);
    type IntoIter = EcoIter<'a, K, V, N>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K: Clone, V: Clone, const N: usize, S: Clone> IntoIterator
    for &'a mut EcoMap<K, V, N, S>
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = EcoIterMut<'a, K, V, N>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K, V, const N: usize, S> IntoIterator for EcoMap<K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, N, S>;

    /// Creates a consuming iterator, that is, one that moves each key-value
    /// pair out of the map in arbitrary order. The map cannot be used after
    /// calling this.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::{EcoMap, EcoVec};
    ///
    /// let map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// // Not possible with .iter()
    /// let vec: EcoVec<(&str, i32)> = map.into_iter().collect();
    /// ```
    #[inline]
    fn into_iter(self) -> IntoIter<K, V, N, S> {
        // SAFETY: We read `self` and prevent the original from dropping.
        let this = ManuallyDrop::new(self);

        match &*this {
            Self::Inline { .. } => {
                // SAFETY: `this` is ManuallyDrop, so the original won't drop.
                let map = unsafe { core::ptr::read(&*this) };
                IntoIter::Inline(map)
            }
            Self::Spilled(rc) => {
                // SAFETY: `this` is ManuallyDrop, so the original won't drop.
                let rc = unsafe { core::ptr::read(rc) };
                match SharedPtr::try_unwrap(rc) {
                    Ok(map) => IntoIter::Spilled(map.into_iter()),
                    Err(rc) => IntoIter::Spilled((*rc).clone().into_iter()),
                }
            }
        }
    }
}

impl<K, V, const N: usize, S> EcoMap<K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
    /// Creates a consuming iterator visiting all the keys in arbitrary order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// let mut vec: Vec<&str> = map.into_keys().collect();
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, ["a", "b", "c"]);
    /// ```
    #[inline]
    pub fn into_keys(self) -> IntoKeys<K, V, N, S> {
        IntoKeys { inner: self.into_iter() }
    }

    /// Creates a consuming iterator visiting all the values in arbitrary order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// let mut vec: Vec<i32> = map.into_values().collect();
    /// // The `IntoValues` iterator produces values in arbitrary order, so
    /// // the values must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    #[inline]
    pub fn into_values(self) -> IntoValues<K, V, N, S> {
        IntoValues { inner: self.into_iter() }
    }
}

impl<K, V, const N: usize, S> PartialEq for EcoMap<K, V, N, S>
where
    K: Eq + Hash,
    V: PartialEq,
    S: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K, V, const N: usize, S> Eq for EcoMap<K, V, N, S>
where
    K: Eq + Hash,
    V: Eq,
    S: BuildHasher,
{
}

impl<K, V, const N: usize, S> fmt::Debug for EcoMap<K, V, N, S>
where
    K: fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, Q, V, const N: usize, S> Index<&Q> for EcoMap<K, V, N, S>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Hash + Eq + ?Sized,
    S: BuildHasher,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Panics
    ///
    /// Panics if the key is not present in the `EcoMap`.
    #[inline]
    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

impl<K, V, const N: usize, S> Drop for EcoMap<K, V, N, S> {
    #[inline]
    fn drop(&mut self) {
        match self {
            Self::Inline { mask, slots, .. } => {
                let mut mask = *mask;
                while mask != 0 {
                    let idx = mask.trailing_zeros() as usize;
                    mask &= mask - 1;

                    // SAFETY: The mask guarantees this slot is initialized.
                    // `slot_read_unchecked` moves the item out and it drops naturally.
                    unsafe { Self::slot_read_unchecked(slots, idx) };
                }
            }
            Self::Spilled(_) => {}
        }
    }
}

impl<K, V, const N: usize, S, const ARR_N: usize> From<[(K, V); ARR_N]>
    for EcoMap<K, V, N, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    /// Converts a `[(K, V); N]` into a `EcoMap<K, V>`.
    ///
    /// If any entries in the array have equal keys,
    /// all but one of the corresponding values will be dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let map1 = EcoMap::<_, _>::from([(1, 2), (3, 4)]);
    /// let map2: EcoMap<_, _> = [(1, 2), (3, 4)].into();
    /// assert_eq!(map1, map2);
    /// ```
    #[inline]
    fn from(arr: [(K, V); ARR_N]) -> Self {
        Self::from_iter(arr)
    }
}

impl<K, V, const N: usize, S> From<HashMap<K, V, S>> for EcoMap<K, V, N, S>
where
    K: Eq + Hash,
    S: BuildHasher + Clone,
{
    fn from(map: HashMap<K, V, S>) -> Self {
        if map.len() <= N {
            let hash_builder = map.hasher().clone();
            let mut slots = [const { MaybeUninit::uninit() }; N];
            let mut mask = 0;

            for (k, v) in map {
                let start_idx = Self::bucket(&k, &hash_builder);
                let ProbeResult::HitEmpty(idx) =
                    Self::probe_index(&slots, mask, start_idx, &k)
                else {
                    // SAFETY: We just created this inline map and `map.len() <= N`,
                    // so there must be at least one empty slot. The key cannot collide
                    // with itself because it's a fresh insertion.
                    unsafe { core::hint::unreachable_unchecked() }
                };

                // SAFETY: `ProbeResult::HitEmpty` guarantees this slot is uninitialized.
                unsafe { Self::slot_write_unchecked(&mut slots, idx, (k, v)) };
                mask |= 1 << idx;
            }

            EcoMap::Inline { mask, slots, hash_builder }
        } else {
            Self::Spilled(SharedPtr::new(map))
        }
    }
}

impl<K, V, const N: usize, S> FromIterator<(K, V)> for EcoMap<K, V, N, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    /// Constructs a `EcoMap<K, V>` from an iterator of key-value pairs.
    ///
    /// If the iterator produces any pairs with equal keys,
    /// all but one of the corresponding values will be dropped.
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> EcoMap<K, V, N, S> {
        let iter = iter.into_iter();
        let mut map = EcoMap::with_capacity(iter.size_hint().0);
        iter.for_each(|(key, value)| {
            map.insert_unique(key, value);
        });
        map
    }
}

impl<'a, K, V, const N: usize, S> FromIterator<(&'a K, &'a V)> for EcoMap<K, V, N, S>
where
    K: Eq + Hash + Clone + 'a,
    V: Clone + 'a,
    S: BuildHasher + Default,
{
    fn from_iter<T: IntoIterator<Item = (&'a K, &'a V)>>(iter: T) -> EcoMap<K, V, N, S> {
        let iter = iter.into_iter();
        let mut map = EcoMap::with_capacity(iter.size_hint().0);
        iter.for_each(|(key, value)| {
            map.insert_unique(key.clone(), value.clone());
        });
        map
    }
}

/// Inserts all new key-values from the iterator and replaces values with existing
/// keys with new values returned from the iterator.
impl<K, V, const N: usize, S> Extend<(K, V)> for EcoMap<K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
    #[inline]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        match self {
            EcoMap::Inline { mask, .. } => {
                let new_len_hint = mask.count_ones() as usize + iter.size_hint().0;
                if new_len_hint > N {
                    self.spill_with_capacity(new_len_hint);
                }

                iter.for_each(move |(k, v)| {
                    self.insert(k, v);
                });
            }
            EcoMap::Spilled(rc) => {
                let spilled = SharedPtr::make_mut(rc);

                spilled.extend(iter);
            }
        }
    }
}

impl<'a, K, V, const N: usize, S> Extend<(&'a K, &'a V)> for EcoMap<K, V, N, S>
where
    K: Eq + Hash + Clone + 'a,
    V: Clone + 'a,
    S: BuildHasher + Clone,
{
    #[inline]
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(|(key, value)| (key.clone(), value.clone())));
    }
}

/// An iterator over the entries of a `EcoMap`.
///
/// This `struct` is created by the [`iter`] method on [`EcoMap`]. See its
/// documentation for more.
///
/// [`iter`]: EcoMap::iter
///
/// # Example
///
/// ```
/// use ecow::EcoMap;
///
/// let map = EcoMap::<_, _>::from([
///     ("a", 1),
/// ]);
/// let iter = map.iter();
/// ```
pub enum EcoIter<'a, K, V, const N: usize> {
    /// Iterates over the slots of an inline map.
    Inline {
        /// The slots of the inline map.
        slots: &'a [MaybeUninit<(K, V)>; N],
        /// A bitmask indicating which slots are occupied.
        mask: u32,
    },
    /// Iterates over the slots of a spilled map.
    Spilled(hash_map::Iter<'a, K, V>),
}

impl<K, V, const N: usize> Clone for EcoIter<'_, K, V, N> {
    #[inline]
    fn clone(&self) -> Self {
        match self {
            Self::Inline { slots, mask } => Self::Inline { slots, mask: *mask },
            Self::Spilled(spilled) => Self::Spilled(spilled.clone()),
        }
    }
}

impl<K, V, const N: usize> Default for EcoIter<'_, K, V, N> {
    #[inline]
    fn default() -> Self {
        Self::Spilled(Default::default())
    }
}

impl<'a, K, V, const N: usize> Iterator for EcoIter<'a, K, V, N> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Inline { slots, mask } => {
                if *mask == 0 {
                    return None;
                }

                let idx = mask.trailing_zeros() as usize;

                // SAFETY: The mask guarantees this slot is initialized.
                let (k, v) = unsafe { EcoMap::<K, V, N>::slot_ref_unchecked(slots, idx) };

                *mask &= *mask - 1;

                Some((k, v))
            }
            Self::Spilled(inner) => inner.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            EcoIter::Inline { .. } => (self.len(), Some(self.len())),
            EcoIter::Spilled(spilled) => spilled.size_hint(),
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }
}

impl<K, V, const N: usize> ExactSizeIterator for EcoIter<'_, K, V, N> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            EcoIter::Inline { mask, .. } => mask.count_ones() as _,
            EcoIter::Spilled(spilled) => spilled.len(),
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug, const N: usize> fmt::Debug for EcoIter<'_, K, V, N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<K, V, const N: usize> FusedIterator for EcoIter<'_, K, V, N> {}

/// A mutable iterator over the entries of a `EcoMap`.
///
/// This `struct` is created by the [`iter_mut`] method on [`EcoMap`]. See its
/// documentation for more.
///
/// [`iter_mut`]: EcoMap::iter_mut
///
/// # Example
///
/// ```
/// use ecow::EcoMap;
///
/// let mut map = EcoMap::<_, _>::from([
///     ("a", 1),
/// ]);
/// let iter = map.iter_mut();
/// ```
pub enum EcoIterMut<'a, K, V, const N: usize> {
    /// Iterates over the slots of an inline map.
    Inline {
        /// The slots of the inline map.
        slots: &'a mut [MaybeUninit<(K, V)>; N],
        /// A bitmask indicating which slots are occupied.
        mask: u32,
    },
    /// Iterates over the slots of a spilled map.
    Spilled(hash_map::IterMut<'a, K, V>),
}

impl<'a, K, V, const N: usize> Iterator for EcoIterMut<'a, K, V, N> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Inline { slots, mask } => {
                if *mask == 0 {
                    return None;
                }

                let idx = mask.trailing_zeros() as usize;

                // SAFETY: The mask guarantees this slot is initialized.
                let (k, v) = unsafe { EcoMap::<K, V, N>::slot_mut_unchecked(slots, idx) };

                *mask &= *mask - 1;

                // SAFETY:
                // 1. We cleared the current slot's bit in `mask` immediately before this block,
                //    guaranteeing subsequent calls to `next()` can never access this index again.
                // 2. Because indexes are never revisited, every yielded `&'a mut V` points to
                //    a completely unique, non-overlapping memory location, ensuring no mutable
                //    aliasing can ever occur.
                unsafe {
                    let k = &*(k as *const K);
                    let v = &mut *(v as *mut V);
                    Some((k, v))
                }
            }
            Self::Spilled(inner) => inner.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            EcoIterMut::Inline { .. } => (self.len(), Some(self.len())),
            EcoIterMut::Spilled(spilled) => spilled.size_hint(),
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }
}

impl<K, V, const N: usize> ExactSizeIterator for EcoIterMut<'_, K, V, N> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            EcoIterMut::Inline { mask, .. } => mask.count_ones() as _,
            EcoIterMut::Spilled(spilled) => spilled.len(),
        }
    }
}

impl<K, V, const N: usize> fmt::Debug for EcoIterMut<'_, K, V, N>
where
    K: fmt::Debug,
    V: fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Inline { slots, mask } => {
                let slots: &[MaybeUninit<(K, V)>; N] = slots;
                let mut active_mask = *mask;
                let mut list = f.debug_list();

                while active_mask != 0 {
                    let idx = active_mask.trailing_zeros() as usize;
                    active_mask &= active_mask - 1;

                    // SAFETY: The mask bit guarantees this slot is initialized.
                    let (key, value) =
                        unsafe { EcoMap::<K, V, N>::slot_ref_unchecked(slots, idx) };
                    list.entry(&(key, value));
                }

                list.finish()
            }
            Self::Spilled(spilled) => fmt::Debug::fmt(spilled, f),
        }
    }
}

impl<K, V, const N: usize> Default for EcoIterMut<'_, K, V, N> {
    #[inline]
    fn default() -> Self {
        Self::Spilled(Default::default())
    }
}

impl<K, V, const N: usize> FusedIterator for EcoIterMut<'_, K, V, N> {}

macro_rules! borrowed_iter_adapter {
    ($(#[$attr:meta])* $name:ident, $item:ty, $next:expr, where $($debug_bound:tt)*) => {
        $(#[$attr])*
        pub struct $name<'a, K, V, const N: usize> {
            inner: EcoIter<'a, K, V, N>,
        }

        impl<'a, K, V, const N: usize> Clone for $name<'a, K, V, N> {
            #[inline]
            fn clone(&self) -> Self {
                Self { inner: self.inner.clone() }
            }
        }

        impl<'a, K, V, const N: usize> Iterator for $name<'a, K, V, N> {
            type Item = $item;

            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                self.inner.next().map($next)
            }

            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.inner.size_hint()
            }

            #[inline]
            fn count(self) -> usize {
                self.inner.count()
            }
        }

        impl<K, V, const N: usize> ExactSizeIterator for $name<'_, K, V, N> {
            #[inline]
            fn len(&self) -> usize {
                self.inner.len()
            }
        }

        impl<K, V, const N: usize> fmt::Debug for $name<'_, K, V, N>
        where
            $($debug_bound)*
        {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_list().entries(self.clone()).finish()
            }
        }

        impl<K, V, const N: usize> Default for $name<'_, K, V, N> {
            #[inline]
            fn default() -> Self {
                Self { inner: EcoIter::default() }
            }
        }

        impl<K, V, const N: usize> FusedIterator for $name<'_, K, V, N> {}
    };
}

borrowed_iter_adapter!(
    /// An iterator over the keys of a `EcoMap`.
    ///
    /// This `struct` is created by the [`keys`] method on [`EcoMap`]. See its
    /// documentation for more.
    ///
    /// [`keys`]: EcoMap::keys
    ///
    /// # Example
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    /// ]);
    /// let iter_keys = map.keys();
    /// ```
    Keys, &'a K, |(key, _)| key, where K: fmt::Debug
);
borrowed_iter_adapter!(
    /// An iterator over the values of a `EcoMap`.
    ///
    /// This `struct` is created by the [`values`] method on [`EcoMap`]. See its
    /// documentation for more.
    ///
    /// [`values`]: EcoMap::values
    ///
    /// # Example
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    /// ]);
    /// let iter_values = map.values();
    /// ```
    Values, &'a V, |(_, value)| value, where V: fmt::Debug
);

/// A mutable iterator over the values of a `EcoMap`.
///
/// This `struct` is created by the [`values_mut`] method on [`EcoMap`]. See its
/// documentation for more.
///
/// [`values_mut`]: EcoMap::values_mut
///
/// # Example
///
/// ```
/// use ecow::EcoMap;
///
/// let mut map = EcoMap::<_, _>::from([
///     ("a", 1),
/// ]);
/// let iter_values = map.values_mut();
/// ```
pub enum ValuesMut<'a, K, V, const N: usize> {
    /// Iterates over the slots of an inline map.
    Inline {
        /// The slots of the inline map.
        slots: &'a mut [MaybeUninit<(K, V)>; N],
        /// A bitmask indicating which slots are occupied.
        mask: u32,
    },
    /// Iterates over the slots of a spilled map.
    Spilled(hash_map::ValuesMut<'a, K, V>),
}

impl<'a, K, V, const N: usize> Iterator for ValuesMut<'a, K, V, N> {
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Inline { slots, mask } => {
                if *mask == 0 {
                    return None;
                }

                let idx = mask.trailing_zeros() as usize;

                // SAFETY: The mask guarantees this slot is initialized.
                let (_, value) =
                    unsafe { EcoMap::<K, V, N>::slot_mut_unchecked(slots, idx) };

                *mask &= *mask - 1;

                // SAFETY: We cleared the current slot's bit in `mask`, so this value
                // cannot be yielded again and cannot alias with future yielded values.
                Some(unsafe { &mut *(value as *mut V) })
            }
            Self::Spilled(spilled) => spilled.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::Inline { .. } => (self.len(), Some(self.len())),
            Self::Spilled(spilled) => spilled.size_hint(),
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }
}

impl<K, V, const N: usize> ExactSizeIterator for ValuesMut<'_, K, V, N> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            ValuesMut::Inline { mask, .. } => mask.count_ones() as _,
            ValuesMut::Spilled(spilled) => spilled.len(),
        }
    }
}

impl<K, V, const N: usize> fmt::Debug for ValuesMut<'_, K, V, N>
where
    V: fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Inline { slots, mask } => {
                let slots: &[MaybeUninit<(K, V)>; N] = slots;
                let mut active_mask = *mask;
                let mut list = f.debug_list();

                while active_mask != 0 {
                    let idx = active_mask.trailing_zeros() as usize;
                    active_mask &= active_mask - 1;

                    // SAFETY: The mask bit guarantees this slot is initialized.
                    let (_, value) =
                        unsafe { EcoMap::<K, V, N>::slot_ref_unchecked(slots, idx) };
                    list.entry(value);
                }

                list.finish()
            }
            Self::Spilled(spilled) => fmt::Debug::fmt(spilled, f),
        }
    }
}

impl<K, V, const N: usize> Default for ValuesMut<'_, K, V, N> {
    #[inline]
    fn default() -> Self {
        Self::Spilled(Default::default())
    }
}

impl<K, V, const N: usize> FusedIterator for ValuesMut<'_, K, V, N> {}

macro_rules! owning_iter_adapter {
    ($(#[$attr:meta])* $name:ident, $item:ty, $next:expr, $debug:expr, where $($debug_bound:tt)*) => {
        $(#[$attr])*
        pub struct $name<K, V, const N: usize, S = DefaultHashBuilder> {
            inner: IntoIter<K, V, N, S>,
        }

        impl<K, V, const N: usize, S> Iterator for $name<K, V, N, S>
        where
            K: Eq + Hash + Clone,
            V: Clone,
            S: BuildHasher + Clone,
        {
            type Item = $item;

            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                self.inner.next().map($next)
            }

            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.inner.size_hint()
            }

            #[inline]
            fn count(self) -> usize {
                self.inner.count()
            }
        }

        impl<K, V, const N: usize, S> ExactSizeIterator for $name<K, V, N, S>
        where
            K: Eq + Hash + Clone,
            V: Clone,
            S: BuildHasher + Clone,
        {
            #[inline]
            fn len(&self) -> usize {
                self.inner.len()
            }
        }

        impl<K, V, const N: usize, S> fmt::Debug for $name<K, V, N, S>
        where
            $($debug_bound)*
        {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_list().entries(self.inner.iter().map($debug)).finish()
            }
        }

        impl<K, V, const N: usize, S> Default for $name<K, V, N, S>
        where
            S: Default,
        {
            #[inline]
            fn default() -> Self {
                Self { inner: IntoIter::default() }
            }
        }

        impl<K, V, const N: usize, S> FusedIterator for $name<K, V, N, S>
        where
            K: Eq + Hash + Clone,
            V: Clone,
            S: BuildHasher + Clone,
        {
        }
    };
}

owning_iter_adapter!(
    /// An owning iterator over the keys of a `EcoMap`.
    ///
    /// This `struct` is created by the [`into_keys`] method on [`EcoMap`].
    /// See its documentation for more.
    ///
    /// [`into_keys`]: EcoMap::into_keys
    ///
    /// # Example
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    /// ]);
    /// let iter_keys = map.into_keys();
    /// ```
    IntoKeys, K, |(key, _)| key, |(key, _)| key, where K: fmt::Debug
);
owning_iter_adapter!(
    /// An owning iterator over the values of a `EcoMap`.
    ///
    /// This `struct` is created by the [`into_values`] method on [`EcoMap`].
    /// See its documentation for more.
    ///
    /// [`into_values`]: EcoMap::into_values
    ///
    /// # Example
    ///
    /// ```
    /// use ecow::EcoMap;
    ///
    /// let map = EcoMap::<_, _>::from([
    ///     ("a", 1),
    /// ]);
    /// let iter_keys = map.into_values();
    /// ```
    IntoValues, V, |(_, value)| value, |(_, value)| value, where V: fmt::Debug
);

/// An owning iterator over the entries of an `EcoMap`.
///
/// This `struct` is created by the [`into_iter`] method on [`EcoMap`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
///
/// # Example
///
/// ```
/// use ecow::EcoMap;
///
/// let map = EcoMap::<_, _>::from([
///     ("a", 1),
/// ]);
/// let iter = map.into_iter();
/// ```
pub enum IntoIter<K, V, const N: usize, S = DefaultHashBuilder> {
    /// Iterates over the slots of an inline map.
    Inline(EcoMap<K, V, N, S>),
    /// Iterates over the slots of a spilled map.
    Spilled(hash_map::IntoIter<K, V>),
}

impl<K, V, const N: usize, S> IntoIter<K, V, N, S> {
    /// Returns an iterator of references over the remaining items.
    #[inline]
    pub(super) fn iter(&self) -> EcoIter<'_, K, V, N> {
        match self {
            Self::Inline(map) => map.iter(),
            Self::Spilled(_) => EcoIter::Spilled(Default::default()),
        }
    }
}

impl<K, V, const N: usize, S> Default for IntoIter<K, V, N, S>
where
    S: Default,
{
    #[inline]
    fn default() -> Self {
        Self::Inline(EcoMap::default())
    }
}

impl<K, V, const N: usize, S> Iterator for IntoIter<K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Inline(map) => {
                let EcoMap::Inline { mask, slots, .. } = map else {
                    unsafe { core::hint::unreachable_unchecked() }
                };

                if *mask == 0 {
                    return None;
                }

                let idx = mask.trailing_zeros() as usize;
                *mask &= *mask - 1;

                // SAFETY: The previous mask bit guaranteed this slot was initialized,
                // and clearing it before reading prevents it from being yielded or
                // dropped again by `EcoMap`'s drop impl.
                Some(unsafe { EcoMap::<K, V, N>::slot_read_unchecked(slots, idx) })
            }
            Self::Spilled(inner) => inner.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }
}

impl<K, V, const N: usize, S> ExactSizeIterator for IntoIter<K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
    #[inline]
    fn len(&self) -> usize {
        match self {
            IntoIter::Inline(map) => map.len(),
            IntoIter::Spilled(inner) => inner.len(),
        }
    }
}

impl<K, V, const N: usize, S> fmt::Debug for IntoIter<K, V, N, S>
where
    K: fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<K, V, const N: usize, S> FusedIterator for IntoIter<K, V, N, S>
where
    K: Eq + Hash + Clone,
    V: Clone,
    S: BuildHasher + Clone,
{
}

#[cfg(feature = "sync")]
mod rayon_impl {
    use super::*;
    use rayon::iter::{Either, IntoParallelIterator, IterBridge, ParallelBridge};

    #[cfg(feature = "std")]
    use rayon::collections::hash_map::{
        IntoIter as ParallelIntoIter, Iter as ParallelIter, IterMut as ParallelIterMut,
    };

    #[cfg(not(feature = "std"))]
    use hashbrown::hash_map::rayon::{
        IntoParIter as ParallelIntoIter, ParIter as ParallelIter,
        ParIterMut as ParallelIterMut,
    };

    impl<'a, K, V, const N: usize, S> IntoParallelIterator for &'a EcoMap<K, V, N, S>
    where
        K: Eq + Hash + Sync,
        V: Sync,
        S: BuildHasher + Sync,
    {
        type Item = (&'a K, &'a V);
        type Iter = Either<IterBridge<EcoIter<'a, K, V, N>>, ParallelIter<'a, K, V>>;

        /// Converts `self` into a parallel iterator.
        ///
        /// # Examples
        ///
        /// ```rust,ignore
        /// // This doctest is ignored under Miri because rayon's dependency
        /// // `crossbeam-epoch` uses integer-to-pointer casts internally,
        /// // which Miri's strict provenance checks flag as a false positive.
        /// // The issue is upstream in crossbeam, not in this crate.
        /// use ecow::EcoMap;
        /// use rayon::prelude::*;
        ///
        /// let mut map = EcoMap::<_, _>::from([
        ///     ("a", 1),
        ///     ("b", 2),
        ///     ("cc", 3),
        /// ]);
        ///
        /// map.into_par_iter().for_each(|(k, v)| println!("{}: {}", k, v));
        /// ```
        #[inline]
        fn into_par_iter(self) -> Self::Iter {
            match self {
                EcoMap::Inline { .. } => Either::Left(self.iter().par_bridge()),
                EcoMap::Spilled(arc) => Either::Right(arc.as_ref().into_par_iter()),
            }
        }
    }

    impl<'a, K, V, const N: usize, S> IntoParallelIterator for &'a mut EcoMap<K, V, N, S>
    where
        K: Send + Eq + Hash + Sync + Clone,
        V: Send + Clone,
        S: BuildHasher + Sync + Clone,
    {
        type Item = (&'a K, &'a mut V);
        type Iter =
            Either<IterBridge<EcoIterMut<'a, K, V, N>>, ParallelIterMut<'a, K, V>>;

        fn into_par_iter(self) -> Self::Iter {
            match self {
                EcoMap::Inline { .. } => Either::Left(self.iter_mut().par_bridge()),
                EcoMap::Spilled(arc) => {
                    let map = SharedPtr::make_mut(arc);
                    Either::Right(map.into_par_iter())
                }
            }
        }
    }

    impl<K, V, const N: usize, S> IntoParallelIterator for EcoMap<K, V, N, S>
    where
        K: Send + Eq + Hash + Sync + Clone,
        V: Send + Sync + Clone,
        S: Send + Sync + BuildHasher + Clone + Default,
    {
        type Item = (K, V);
        type Iter = Either<IterBridge<IntoIter<K, V, N, S>>, ParallelIntoIter<K, V>>;

        fn into_par_iter(self) -> Self::Iter {
            // Freeze the automatic destructor
            let managed_self = ManuallyDrop::new(self);

            match &*managed_self {
                EcoMap::Inline { mask, slots, hash_builder } => {
                    // Unpack fields
                    let mask = *mask;
                    let slots = unsafe { core::ptr::read(slots) };
                    let hash_builder = unsafe { core::ptr::read(hash_builder) };

                    let inline_map = EcoMap::Inline { mask, slots, hash_builder };

                    Either::Left(inline_map.into_iter().par_bridge())
                }
                EcoMap::Spilled(arc) => {
                    // SAFETY: managed_self is ManuallyDrop, so the original map won't drop this Arc.
                    let arc = unsafe { core::ptr::read(arc) };

                    Either::Right(SharedPtr::unwrap_or_clone(arc).into_par_iter())
                }
            }
        }
    }

    unsafe impl<K: Send, V: Send, const N: usize, S: Send> Send for EcoMap<K, V, N, S> {}
    unsafe impl<K: Sync, V: Sync, const N: usize, S: Sync> Sync for EcoMap<K, V, N, S> {}
}

#[cfg(feature = "serde")]
mod serde {
    use core::{
        fmt,
        hash::{BuildHasher, Hash},
        marker::PhantomData,
    };

    use serde::de::{MapAccess, Visitor};

    use crate::EcoMap;

    // Serialize: Simply view the map as a collection of items
    impl<K, V, const N: usize, S> serde::Serialize for EcoMap<K, V, N, S>
    where
        K: serde::Serialize + Eq + Hash,
        V: serde::Serialize,
    {
        fn serialize<S_>(&self, serializer: S_) -> Result<S_::Ok, S_::Error>
        where
            S_: serde::Serializer,
        {
            serializer.collect_map(self.iter())
        }
    }

    struct EcoMapVisitor<K, V, const N: usize, S>(PhantomData<(K, V, S)>);

    impl<'de, K, V, const N: usize, S> Visitor<'de> for EcoMapVisitor<K, V, N, S>
    where
        K: serde::Deserialize<'de> + Eq + Hash + Clone,
        V: serde::Deserialize<'de> + Clone,
        S: BuildHasher + Default + Clone,
    {
        type Value = EcoMap<K, V, N, S>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a map of keys and values")
        }

        fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
        where
            A: MapAccess<'de>,
        {
            let mut eco = EcoMap::with_capacity(map.size_hint().unwrap_or(0));
            while let Some((k, v)) = map.next_entry()? {
                eco.insert(k, v);
            }
            Ok(eco)
        }
    }

    impl<'de, K, V, const N: usize, S> serde::Deserialize<'de> for EcoMap<K, V, N, S>
    where
        K: serde::Deserialize<'de> + Eq + Hash + Clone,
        V: serde::Deserialize<'de> + Clone,
        S: BuildHasher + Default + Clone,
    {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            deserializer.deserialize_map(EcoMapVisitor(PhantomData))
        }
    }
}
