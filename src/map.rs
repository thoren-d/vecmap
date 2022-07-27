use std::{borrow::Borrow, fmt::Debug, iter::FromIterator, marker::PhantomData, ops::Index};

use crate::{BinarySearch, LinearSearch, SearchStrategy};

#[derive(Clone)]
pub struct Map<S, K, V> {
    entries: Vec<(K, V)>,
    _strategy: PhantomData<S>,
}

pub type BinaryMap<K, V> = Map<BinarySearch, K, V>;
pub type LinearMap<K, V> = Map<LinearSearch, K, V>;

impl<S: SearchStrategy, K, V> Map<S, K, V> {
    /// Creates an empty Map.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    /// let map: LinearMap<u8, usize> = LinearMap::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Map {
            entries: Vec::new(),
            _strategy: PhantomData,
        }
    }

    /// Creates an empty Map with the specified capactiy.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    /// let map: BinaryMap<u8, usize> = BinaryMap::with_capacity(42);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Map {
            entries: Vec::with_capacity(capacity),
            _strategy: PhantomData,
        }
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the map might be able to hold
    /// more, but is guaranteed to be able to hold at least this many.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    /// let map: LinearMap<i32, i32> = LinearMap::with_capacity(100);
    /// assert!(map.capacity() >= 100);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.entries.capacity()
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory
    /// for reuse.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut a = LinearMap::new();
    /// a.insert(1, "a");
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut a = BinaryMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut a = LinearMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Clears the map, returning all key-value pairs as an iterator. Keeps the
    /// allocated memory for reuse.
    ///
    /// If the returned iterator is dropped before being fully consumed, it
    /// drops the remaining key-value pairs. The returned iterator keeps a
    /// mutable borrow on the vector to optimize its implementation.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut a = BinaryMap::new();
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
    pub fn drain(&mut self) -> impl Iterator<Item = (K, V)> + '_ {
        let len = self.len();
        self.entries.drain(0..len)
    }

    /// Creates a consuming iterator visiting all the keys in arbitrary order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `K`.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let map = LinearMap::from([
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
    pub fn into_keys(self) -> impl Iterator<Item = K> {
        self.entries.into_iter().map(|(k, _)| k)
    }

    /// Creates a consuming iterator visiting all the values in arbitrary order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `V`.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let map = BinaryMap::from([
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
    pub fn into_values(self) -> impl Iterator<Item = V> {
        self.entries.into_iter().map(|(_, v)| v)
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// The iterator element type is `(&'a K, &'a V)`.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let map = LinearMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {key} val: {val}");
    /// }
    /// ```
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = (&'_ K, &'_ V)> {
        self.entries.iter().map(|(k, v)| (k, v))
    }

    /// An iterator visiting all key-value pairs in arbitrary order,
    /// with mutable references to the values.
    /// The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map = BinaryMap::from([
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
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&'_ K, &'_ mut V)> {
        self.entries.iter_mut().map(|(k, v)| (&*k, v))
    }

    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let map = LinearMap::from([
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
    pub fn keys(&self) -> impl Iterator<Item = &'_ K> {
        self.entries.iter().map(|(k, _)| k)
    }

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a V`.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let map = BinaryMap::from([
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
    pub fn values(&self) -> impl Iterator<Item = &'_ V> {
        self.entries.iter().map(|(_, v)| v)
    }

    /// An iterator visiting all values mutably in arbitrary order.
    /// The iterator element type is `&'a mut V`.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let map = BinaryMap::from([
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
    pub fn values_mut(&mut self) -> impl Iterator<Item = &'_ mut V> {
        self.entries.iter_mut().map(|(_, v)| v)
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `HashMap`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Panics
    /// Panics if the new allocation size overflows [`usize`].
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    /// let mut map: LinearMap<&str, i32> = LinearMap::new();
    /// map.reserve(10);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.entries.reserve(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// in the given map. The collection may reserve more space to avoid frequent
    /// reallocations.
    ///
    /// # Errors
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map: BinaryMap<&str, isize> = BinaryMap::new();
    /// map.try_reserve(10).expect("why is the test harness OOMing on 10 bytes?");
    /// ```
    #[inline]
    pub fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<(), std::collections::TryReserveError> {
        self.entries.try_reserve(additional)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` for which `f(&k, &mut v)` returns `false`.
    /// The elements are visited in unsorted (and unspecified) order.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut map: LinearMap<i32, i32> = (0..8).map(|x| (x, x*10)).collect();
    /// map.retain(|&k, _| k % 2 == 0);
    /// assert_eq!(map.len(), 4);
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        self.entries.retain_mut(|(k, v)| f(&*k, v))
    }

    /// Shrinks the capacity of the map with a lower limit. It will drop
    /// down no lower than the supplied limit while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map: BinaryMap<i32, i32> = BinaryMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10);
    /// map.shrink_to(0);
    /// assert!(map.capacity() >= 2);
    /// ```
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.entries.shrink_to(min_capacity);
    }

    /// Shrinks the capacity of the map as much as possible. It will drop
    /// down as much as possible while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut map: LinearMap<i32, i32> = LinearMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.entries.shrink_to_fit();
    }
}

impl<S: SearchStrategy, K, V> Default for Map<S, K, V> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

pub struct Iter<'a, K, V> {
    inner: std::slice::Iter<'a, (K, V)>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, v)| (k, v))
    }
}

pub struct IterMut<'a, K, V> {
    inner: std::slice::IterMut<'a, (K, V)>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V>
where
    K: 'a,
    V: 'a,
{
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, v)| (&*k, v))
    }
}

impl<'a, S: SearchStrategy, K, V> IntoIterator for &'a mut Map<S, K, V> {
    type Item = (&'a K, &'a mut V);

    type IntoIter = IterMut<'a, K, V>;

    /// Creates a mutable iterator over each key-value pair in the map in
    /// arbitrary (for linear maps) or sorted (for binary maps) order.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut map = LinearMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// let vec: Vec<(&&str, &mut i32)> = (&mut map).into_iter().collect();
    /// assert_eq!(vec, vec![(&"a", &mut 1), (&"b", &mut 2), (&"c", &mut 3)]);
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IterMut {
            inner: self.entries.iter_mut(),
        }
    }
}

impl<'a, S: SearchStrategy, K, V> IntoIterator for &'a Map<S, K, V> {
    type Item = (&'a K, &'a V);

    type IntoIter = Iter<'a, K, V>;

    /// Creates an iterator over each key-value pair in the map in arbitrary (for linear maps)
    /// or sorted (for binary maps) order.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let map = BinaryMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// let vec: Vec<(&&str, &i32)> = (&map).into_iter().collect();
    /// assert_eq!(vec, vec![(&"a", &1), (&"b", &2), (&"c", &3)]);
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            inner: self.entries.iter(),
        }
    }
}

pub struct IntoIter<K, V> {
    inner: std::vec::IntoIter<(K, V)>,
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<S: SearchStrategy, K, V> IntoIterator for Map<S, K, V> {
    type Item = (K, V);

    type IntoIter = IntoIter<K, V>;

    /// Creates a consuming iterator, that is, one that moves each key-value
    /// pair out of the map in arbitrary order. The map cannot be used after
    /// calling this.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let map = LinearMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// // Not possible with .iter()
    /// let vec: Vec<(&str, i32)> = map.into_iter().collect();
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.entries.into_iter(),
        }
    }
}

impl<K: Eq, V> Map<LinearSearch, K, V> {
    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut map = LinearMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    #[inline(always)]
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        self.get(key).is_some()
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut letters = LinearMap::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     let counter = letters.entry(ch).or_insert(0);
    ///     *counter += 1;
    /// }
    ///
    /// assert_eq!(letters[&'s'], 2);
    /// assert_eq!(letters[&'t'], 3);
    /// assert_eq!(letters[&'u'], 1);
    /// assert_eq!(letters.get(&'y'), None);
    /// ```
    #[inline(always)]
    pub fn entry(&mut self, key: K) -> Entry<LinearSearch, K, V> {
        match self
            .entries
            .iter()
            .enumerate()
            .find(|(_, (k, _))| *k == key)
        {
            Some((index, _)) => Entry::Occupied(OccupiedEntry {
                key,
                index,
                map: self,
            }),
            None => Entry::Vacant(VacantEntry {
                key,
                index: self.entries.len(),
                map: self,
            }),
        }
    }

    /// Returns a reference to the value with the corresponding key.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    /// let mut map = LinearMap::<String, i32>::new();
    /// assert_eq!(map.insert("hello".into(), 42), None);
    /// assert_eq!(map.get("hello"), Some(&42));
    /// ```
    #[inline(always)]
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.entries
            .iter()
            .find_map(|(k, v)| if key == k.borrow() { Some(v) } else { None })
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut map = LinearMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"a")));
    /// assert_eq!(map.get_key_value(&2), None);
    /// ```
    #[inline(always)]
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.entries.iter().find_map(|(k, v)| {
            if key == k.borrow() {
                Some((k, v))
            } else {
                None
            }
        })
    }

    /// Returns a reference to the value with the corresponding key.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    /// let mut map = LinearMap::<String, i32>::new();
    /// assert_eq!(map.insert("hello".into(), 42), None);
    /// assert_eq!(map.get_mut("hello"), Some(&mut 42));
    /// ```
    #[inline(always)]
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.entries.iter_mut().find_map(
            |(k, v)| {
                if key == (&*k).borrow() {
                    Some(v)
                } else {
                    None
                }
            },
        )
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not already have this key present, [`None`](None) is returned.
    /// If the map did have this key present, the value is updated, and the old value is returned. The key is not updated, though.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    /// let mut map = LinearMap::new();
    /// assert_eq!(map.insert("hello", 42), None);
    /// assert_eq!(map.insert("hello", 69), Some(42));
    /// ```
    #[inline(always)]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.entries.iter_mut().find(|(k, _)| *k == key) {
            Some((_, v)) => Some(std::mem::replace(v, value)),
            None => {
                self.entries.push((key, value));
                None
            }
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut map = LinearMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    #[inline(always)]
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.remove_entry(key).map(|(_, v)| v)
    }

    /// Removes a key from the map, returning the stored key and value if the
    /// key was previously in the map.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut map = LinearMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove_entry(&1), Some((1, "a")));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    #[inline(always)]
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        let idx = self.entries.iter().enumerate().find_map(|(i, (k, _))| {
            if *k.borrow() == *key {
                Some(i)
            } else {
                None
            }
        });
        idx.map(|idx| self.remove_at(idx))
    }

    #[inline(always)]
    fn remove_at(&mut self, index: usize) -> (K, V) {
        self.entries.swap_remove(index)
    }
}

impl<K: Ord + Eq, V> Map<BinarySearch, K, V> {
    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map = BinaryMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    #[inline(always)]
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Ord,
    {
        self.get(key).is_some()
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut letters = LinearMap::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     let counter = letters.entry(ch).or_insert(0);
    ///     *counter += 1;
    /// }
    ///
    /// assert_eq!(letters[&'s'], 2);
    /// assert_eq!(letters[&'t'], 3);
    /// assert_eq!(letters[&'u'], 1);
    /// assert_eq!(letters.get(&'y'), None);
    /// ```
    #[inline(always)]
    pub fn entry(&mut self, key: K) -> Entry<BinarySearch, K, V> {
        match self.entries.binary_search_by(|(k, _)| k.cmp(&key)) {
            Ok(index) => Entry::Occupied(OccupiedEntry {
                index,
                key,
                map: self,
            }),
            Err(index) => Entry::Vacant(VacantEntry {
                index,
                key,
                map: self,
            }),
        }
    }

    /// Returns a reference to the value with the corresponding key.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    /// let mut map = BinaryMap::<String, i32>::new();
    /// assert_eq!(map.insert("hello".into(), 42), None);
    /// assert_eq!(map.get("hello"), Some(&42));
    /// ```
    #[inline(always)]
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Ord + ?Sized,
    {
        match self.entries.binary_search_by(|(k, _)| k.borrow().cmp(key)) {
            Ok(idx) => self.entries.get(idx).map(|(_, v)| v),
            Err(_) => None,
        }
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map = BinaryMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"a")));
    /// assert_eq!(map.get_key_value(&2), None);
    /// ```
    #[inline(always)]
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + Ord + ?Sized,
    {
        match self.entries.binary_search_by(|(k, _)| k.borrow().cmp(key)) {
            Ok(idx) => self.entries.get(idx).map(|(k, v)| (k, v)),
            Err(_) => None,
        }
    }

    /// Returns a reference to the value with the corresponding key.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    /// let mut map = BinaryMap::<String, i32>::new();
    /// assert_eq!(map.insert("hello".into(), 42), None);
    /// assert_eq!(map.get_mut("hello"), Some(&mut 42));
    /// ```
    #[inline(always)]
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + Ord + ?Sized,
    {
        match self.entries.binary_search_by(|(k, _)| k.borrow().cmp(key)) {
            Ok(idx) => self.entries.get_mut(idx).map(|(_, v)| v),
            Err(_) => None,
        }
    }

    /// See [`LinearMap::insert`](crate::LinearMap::insert).
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    /// let mut map = BinaryMap::new();
    /// assert_eq!(map.insert("hello", 42), None);
    /// assert_eq!(map.insert("hello", 69), Some(42));
    /// ```
    #[inline(always)]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.entries.binary_search_by(|(k, _)| k.cmp(&key)) {
            Ok(idx) => Some(std::mem::replace(&mut self.entries[idx].1, value)),
            Err(idx) => {
                self.entries.insert(idx, (key, value));
                None
            }
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map = BinaryMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    #[inline(always)]
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + Ord + ?Sized,
    {
        self.remove_entry(key).map(|(_, v)| v)
    }

    /// Removes a key from the map, returning the stored key and value if the
    /// key was previously in the map.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map = BinaryMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove_entry(&1), Some((1, "a")));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    #[inline(always)]
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Eq + Ord + ?Sized,
    {
        let idx = self.entries.binary_search_by(|(k, _)| k.borrow().cmp(key));
        match idx {
            Ok(idx) => Some(self.remove_at(idx)),
            Err(_) => None,
        }
    }

    #[inline(always)]
    fn remove_at(&mut self, index: usize) -> (K, V) {
        self.entries.remove(index)
    }
}

impl<K: Eq, V> FromIterator<(K, V)> for Map<LinearSearch, K, V> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (min, max) = iter.size_hint();
        let mut res = Self::with_capacity(max.unwrap_or(min));

        for (k, v) in iter {
            res.insert(k, v);
        }

        res
    }
}

impl<K: Eq + Ord, V> FromIterator<(K, V)> for Map<BinarySearch, K, V> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let min_size = iter.size_hint().0;

        // Building large collections with insert amounts to insertion sort,
        // which has O(N^2) runtime, but works well on small collections.
        // For larger ones, use a good sorting algorithm and remove duplicates.
        // TODO: Use a better heuristic for what counts as a "large" collection.
        if min_size > 1000 {
            let mut entries = Vec::from_iter(iter);
            entries.sort_by(|a, b| a.0.cmp(&b.0));
            entries.dedup_by(|a, b| a.0 == b.0);
            Self {
                entries,
                _strategy: PhantomData,
            }
        } else {
            let mut res = Self::with_capacity(min_size);
            for (k, v) in iter {
                res.insert(k, v);
            }
            res
        }
    }
}

impl<K: Eq, V, const N: usize> From<[(K, V); N]> for Map<LinearSearch, K, V> {
    #[inline]
    fn from(entries: [(K, V); N]) -> Self {
        Self::from_iter(entries.into_iter())
    }
}

impl<K: Eq + Ord, V, const N: usize> From<[(K, V); N]> for Map<BinarySearch, K, V> {
    #[inline]
    fn from(entries: [(K, V); N]) -> Self {
        Self::from_iter(entries.into_iter())
    }
}

impl<K, Q: ?Sized, V> Index<&Q> for LinearMap<K, V>
where
    K: Eq + Borrow<Q>,
    Q: Eq,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Panics
    /// Panics if key is not present in the `Map`.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let map = LinearMap::from([("a", 1), ("b", 2)]);
    /// assert_eq!(map["b"], 2);
    /// ```
    #[inline(always)]
    fn index(&self, index: &Q) -> &Self::Output {
        self.get(index).expect("key not found")
    }
}

impl<K, Q: ?Sized, V> Index<&Q> for BinaryMap<K, V>
where
    K: Eq + Ord + Borrow<Q>,
    Q: Eq + Ord,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Panics
    /// Panics if key is not present in the `Map`.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let map = BinaryMap::from([("a", 1), ("b", 2)]);
    /// assert_eq!(map["b"], 2);
    /// ```
    #[inline(always)]
    fn index(&self, index: &Q) -> &Self::Output {
        self.get(index).expect("key not found")
    }
}

impl<S: SearchStrategy, K: Debug, V: Debug> Debug for Map<S, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: Eq, V> Extend<(K, V)> for Map<LinearSearch, K, V> {
    /// Extends the map with key-value pairs from an iterator.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut map = LinearMap::from([("a", 1)]);
    /// map.extend([("b", 2), ("c", 3)].into_iter());
    ///
    /// assert_eq!(map.get("b"), Some(&2));
    /// ```
    #[inline]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        let (count, _) = iter.size_hint();
        self.entries.reserve(count);

        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<'a, K: Eq + Copy + 'a, V: Copy + 'a> Extend<(&'a K, &'a V)> for Map<LinearSearch, K, V> {
    /// Extends the map with key-value pairs from an iterator.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut map = LinearMap::from([("a", 1)]);
    /// map.extend([("b", 2), ("c", 3)].into_iter());
    ///
    /// assert_eq!(map.get("b"), Some(&2));
    /// ```
    #[inline]
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        let (count, _) = iter.size_hint();
        self.entries.reserve(count);

        for (k, v) in iter {
            self.insert(*k, *v);
        }
    }
}

impl<K: Eq + Ord, V> Extend<(K, V)> for Map<BinarySearch, K, V> {
    /// Extends the map with key-value pairs from an iterator.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map = BinaryMap::from([("a", 1)]);
    /// map.extend([("b", 2), ("c", 3)].into_iter());
    ///
    /// assert_eq!(map.get("b"), Some(&2));
    /// ```
    #[inline]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        let (count, _) = iter.size_hint();
        self.entries.reserve(count);

        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<'a, K: Eq + Ord + Copy + 'a, V: Copy + 'a> Extend<(&'a K, &'a V)> for Map<BinarySearch, K, V> {
    /// Extends the map with key-value pairs from an iterator.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map = BinaryMap::from([("a", 1)]);
    /// map.extend([("b", 2), ("c", 3)].into_iter());
    ///
    /// assert_eq!(map.get("b"), Some(&2));
    /// ```
    #[inline]
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        let (count, _) = iter.size_hint();
        self.entries.reserve(count);

        for (k, v) in iter {
            self.insert(*k, *v);
        }
    }
}

impl<K, V> PartialEq<LinearMap<K, V>> for LinearMap<K, V>
where
    K: Eq,
    V: PartialEq,
{
    fn eq(&self, other: &LinearMap<K, V>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        for (k, v) in self.iter() {
            let value = other.get(k);
            match value {
                Some(value) => {
                    if value.ne(v) {
                        return false;
                    }
                }
                None => return false,
            }
        }

        true
    }
}

impl<K: Eq, V: Eq> Eq for LinearMap<K, V> {}

impl<K, V> PartialEq<BinaryMap<K, V>> for BinaryMap<K, V>
where
    K: Eq + Ord,
    V: PartialEq,
{
    fn eq(&self, other: &BinaryMap<K, V>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        for (k, v) in self.iter() {
            let value = other.get(k);
            match value {
                Some(value) => {
                    if value.ne(v) {
                        return false;
                    }
                }
                None => return false,
            }
        }

        true
    }
}
impl<K: Eq + Ord, V: Eq> Eq for BinaryMap<K, V> {}

pub struct OccupiedEntry<'a, S, K, V> {
    key: K,
    index: usize,
    map: &'a mut Map<S, K, V>,
}

impl<'a, S: SearchStrategy, K, V> OccupiedEntry<'a, S, K, V> {
    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: LinearMap<&str, u32> = LinearMap::new();
    /// map.entry("hello").or_insert(42);
    ///
    /// if let Entry::Occupied(o) = map.entry("hello") {
    ///     assert_eq!(o.get(), &42);
    /// }
    /// ```
    #[inline]
    pub fn get(&self) -> &V {
        &self.map.entries[self.index].1
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: BinaryMap<&str, u32> = BinaryMap::new();
    /// map.entry("hello").or_insert(42);
    ///
    /// if let Entry::Occupied(mut o) = map.entry("hello") {
    ///     assert_eq!(o.get_mut(), &42);
    /// }
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.map.entries[self.index].1
    }

    /// Sets the value of the entry, and returns the entry's old value.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: LinearMap<&str, u32> = LinearMap::new();
    /// map.entry("hello").or_insert(42);
    ///
    /// if let Entry::Occupied(mut o) = map.entry("hello") {
    ///     assert_eq!(o.insert(69), 42);
    /// }
    ///
    /// assert_eq!(map["hello"], 69);
    /// ```
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        let (_, v) = &mut self.map.entries[self.index];
        std::mem::replace(v, value)
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: Self::get_mut
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: LinearMap<&str, u32> = LinearMap::new();
    /// map.entry("hello").or_insert(12);
    ///
    /// assert_eq!(map["hello"], 12);
    /// if let Entry::Occupied(o) = map.entry("hello") {
    ///     *o.into_mut() += 10;
    /// }
    ///
    /// assert_eq!(map["hello"], 22);
    /// ```
    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        let Self { key: _, index, map } = self;
        &mut map.entries[index].1
    }

    /// Gets a reference to the key in the entry.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map: BinaryMap<&str, u32> = BinaryMap::new();
    /// map.entry("hello").or_insert(12);
    /// assert_eq!(map.entry("hello").key(), &"hello");
    /// ```
    #[inline]
    pub fn key(&self) -> &K {
        &self.key
    }
}

impl<'a, K: Eq, V> OccupiedEntry<'a, LinearSearch, K, V> {
    /// Takes the value out of the entry, and returns it.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: LinearMap<&str, u32> = LinearMap::new();
    /// map.entry("hello").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("hello") {
    ///     assert_eq!(o.remove(), 12);
    /// }
    ///
    /// assert_eq!(map.contains_key("hello"), false);
    /// ```
    #[inline]
    pub fn remove(self) -> V {
        self.map.remove_at(self.index).1
    }

    /// Take the ownership of the key and value from the map.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: LinearMap<&str, u32> = LinearMap::new();
    /// map.entry("hello").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("hello") {
    ///     // We delete the entry from the map.
    ///     o.remove_entry();
    /// }
    ///
    /// assert_eq!(map.contains_key("hello"), false);
    /// ```
    #[inline]
    pub fn remove_entry(self) -> (K, V) {
        self.map.remove_at(self.index)
    }
}

impl<'a, K: Eq + Ord, V> OccupiedEntry<'a, BinarySearch, K, V> {
    /// Takes the value out of the entry, and returns it.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: BinaryMap<&str, u32> = BinaryMap::new();
    /// map.entry("hello").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("hello") {
    ///     assert_eq!(o.remove(), 12);
    /// }
    ///
    /// assert_eq!(map.contains_key("hello"), false);
    /// ```
    #[inline]
    pub fn remove(self) -> V {
        self.map.remove_at(self.index).1
    }

    /// Take the ownership of the key and value from the map.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: BinaryMap<&str, u32> = BinaryMap::new();
    /// map.entry("hello").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("hello") {
    ///     // We delete the entry from the map.
    ///     o.remove_entry();
    /// }
    ///
    /// assert_eq!(map.contains_key("hello"), false);
    /// ```
    #[inline]
    pub fn remove_entry(self) -> (K, V) {
        self.map.remove_at(self.index)
    }
}

impl<'a, S: SearchStrategy, K: Debug, V: Debug> Debug for OccupiedEntry<'a, S, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("key", &self.key)
            .field("value", self.get())
            .finish_non_exhaustive()
    }
}

pub struct VacantEntry<'a, S, K, V> {
    key: K,
    index: usize,
    map: &'a mut Map<S, K, V>,
}

impl<'a, S: SearchStrategy, K, V> VacantEntry<'a, S, K, V> {
    /// Sets the value of the entry with the `VacantEntry`'s key and returns a mutable reference to it.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: BinaryMap<&str, u32> = BinaryMap::new();
    ///
    /// if let Entry::Vacant(o) = map.entry("hello") {
    ///     o.insert(37);
    /// }
    /// assert_eq!(map["hello"], 37);
    /// ```
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        let Self { key, index, map } = self;
        map.entries.insert(index, (key, value));
        &mut map.entries[index].1
    }

    /// Take ownership of the key.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: LinearMap<&str, u32> = LinearMap::new();
    ///
    /// if let Entry::Vacant(v) = map.entry("hello") {
    ///     assert_eq!(v.into_key(), "hello");
    /// }
    /// ```
    #[inline]
    pub fn into_key(self) -> K {
        self.key
    }

    /// Gets a reference to the key that would be used when inserting a value
    /// through the `VacantEntry`.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map: BinaryMap<&str, u32> = BinaryMap::new();
    /// assert_eq!(map.entry("hello").key(), &"hello");
    /// ```
    #[inline]
    pub fn key(&self) -> &K {
        &self.key
    }
}

impl<'a, S: SearchStrategy, K: Debug, V: Debug> Debug for VacantEntry<'a, S, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VacantEntry")
            .field("key", &self.key)
            .finish_non_exhaustive()
    }
}

pub enum Entry<'a, S, K, V> {
    Occupied(OccupiedEntry<'a, S, K, V>),
    Vacant(VacantEntry<'a, S, K, V>),
}

impl<'a, S: SearchStrategy, K, V> Entry<'a, S, K, V> {
    /// Provides in-place mutable access to an occupied entry before any potential inserts into the map.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map: BinaryMap<&str, u32> = BinaryMap::new();
    ///
    /// map.entry("hello")
    ///    .and_modify(|e| { *e += 1; })
    ///    .or_insert(42);
    /// assert_eq!(map["hello"], 42);
    ///
    /// map.entry("hello")
    ///    .and_modify(|e| { *e += 1; })
    ///    .or_insert(42);
    /// assert_eq!(map["hello"], 43);
    /// ```
    #[inline]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }

    /// Returns a reference to this entry's key.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map: BinaryMap<&str, u32> = BinaryMap::new();
    /// assert_eq!(map.entry("hello").key(), &"hello");
    /// ```
    #[inline]
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(entry) => &entry.key,
            Entry::Vacant(entry) => &entry.key,
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut map: LinearMap<&str, u32> = LinearMap::new();
    ///
    /// map.entry("hello").or_insert(3);
    /// assert_eq!(map["hello"], 3);
    ///
    /// *map.entry("hello").or_insert(10) *= 2;
    /// assert_eq!(map["hello"], 6);
    /// ```
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map: BinaryMap<&str, String> = BinaryMap::new();
    /// let s = "world".to_string();
    ///
    /// map.entry("hello").or_insert_with(|| s);
    ///
    /// assert_eq!(map["hello"], "world".to_string());
    /// ```
    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
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
    /// ```
    /// use vecmap::LinearMap;
    ///
    /// let mut map: LinearMap<&str, usize> = LinearMap::new();
    ///
    /// map.entry("hello").or_insert_with_key(|key| key.chars().count());
    ///
    /// assert_eq!(map["hello"], 5);
    /// ```
    #[inline]
    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let default = default(entry.key());
                entry.insert(default)
            }
        }
    }
}

impl<'a, S: SearchStrategy, K, V> Entry<'a, S, K, V>
where
    V: Default,
{
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::BinaryMap;
    ///
    /// let mut map: BinaryMap<&str, Option<u32>> = BinaryMap::new();
    /// map.entry("hello").or_default();
    ///
    /// assert_eq!(map["hello"], None);
    /// ```
    #[inline]
    pub fn or_default(self) -> &'a mut V {
        self.or_insert_with(|| V::default())
    }
}

impl<'a, S: SearchStrategy, K: Debug, V: Debug> Debug for Entry<'a, S, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Occupied(entry) => entry.fmt(f),
            Self::Vacant(entry) => entry.fmt(f),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new_binary() {
        let _map = BinaryMap::<u8, usize>::new();
    }

    #[test]
    fn with_capacity_linear() {
        let _map = LinearMap::<u8, usize>::with_capacity(16);
    }

    #[test]
    fn implements_debug() {
        let map = BinaryMap::from([("a", 1), ("b", 2), ("c", 3)]);
        let _res = format!("map: {:?}", map);
    }

    #[test]
    fn map_equality_linear() {
        let a = LinearMap::from([("a", 1), ("b", 2), ("c", 3)]);
        let b = LinearMap::from([("c", 3), ("a", 1), ("b", 2)]);
        let c = LinearMap::from([("c", 3), ("a", 1), ("t", 2)]);
        let d = LinearMap::from([("c", 3), ("a", 1), ("t", 2), ("s", 4)]);

        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_ne!(b, c);
        assert_ne!(a, d);
        assert_ne!(a, c);
    }

    #[test]
    fn map_equality_binary() {
        let a = BinaryMap::from([("a", 1), ("b", 2), ("c", 3)]);
        let b = BinaryMap::from([("c", 3), ("a", 1), ("b", 2)]);
        let c = BinaryMap::from([("c", 3), ("a", 1), ("t", 2)]);
        let d = BinaryMap::from([("c", 3), ("a", 1), ("t", 2), ("s", 4)]);

        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_ne!(b, c);
        assert_ne!(a, d);
        assert_ne!(a, c);
    }
}
