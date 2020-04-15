use std::cmp::Ord;

pub struct VecMap<K, V> {
    items: Vec<(K, V)>,
}

pub struct EntryData<'a, K, V> {
    index: usize,
    key: K,
    map: &'a mut VecMap<K, V>,
}

pub enum Entry<'a, K, V> {
    Occupied(EntryData<'a, K, V>),
    Vacant(EntryData<'a, K, V>),
}

impl<K: Ord, V> Default for VecMap<K, V> {
    fn default() -> Self {
        VecMap::new()
    }
}

impl<K: Ord, V> VecMap<K, V> {
    pub fn new() -> Self {
        VecMap { items: Vec::new() }
    }

    #[inline]
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        match self.items.binary_search_by_key(&&k, |item| &item.0) {
            Ok(idx) => {
                let mut res = v;
                std::mem::swap(&mut res, &mut self.items[idx].1);
                Some(res)
            }
            Err(idx) => {
                self.items.insert(idx, (k, v));
                None
            }
        }
    }

    #[inline]
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        match self.items.binary_search_by_key(&&key, |item| &item.0) {
            Ok(idx) => Entry::Occupied(EntryData {
                index: idx,
                key,
                map: self,
            }),
            Err(idx) => Entry::Vacant(EntryData {
                index: idx,
                key,
                map: self,
            }),
        }
    }

    pub fn get_at(&self, index: usize) -> &V {
        &self.items[index].1
    }

    #[inline]
    pub fn get(&self, key: &K) -> Option<&V> {
        match self.items.binary_search_by_key(&key, |item| &item.0) {
            Ok(idx) => Some(&self.items[idx].1),
            Err(_) => None,
        }
    }
}

impl<'a, K: Ord, V> Entry<'a, K, V> {
    #[inline]
    pub fn insert(self, v: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => {
                entry.map.items[entry.index] = (entry.key, v);
                &mut entry.map.items[entry.index].1
            }
            Entry::Vacant(entry) => {
                entry.map.items.insert(entry.index, (entry.key, v));
                &mut entry.map.items[entry.index].1
            }
        }
    }

    #[inline]
    pub fn or_insert(self, v: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => &mut entry.map.items[entry.index].1,
            Entry::Vacant(_) => self.insert(v),
        }
    }
}
