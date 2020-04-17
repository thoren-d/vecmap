pub mod vecmap;
pub use crate::vecmap::VecMap;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_keeps_order() {
        let mut map: VecMap<i32, i32> = VecMap::new();
        map.insert(1, 10);
        map.insert(-2, 20);
        assert_eq!(map.get_at(0), &20);
        assert_eq!(map.get_at(1), &10);
    }

    #[test]
    fn insert_smoke() {
        let mut map: VecMap<i32, i32> = VecMap::new();
        map.insert(1, 11);
        map.insert(5, 15);
        map.insert(3, 13);
        assert_eq!(map.get(&1), Some(&11));
        assert_eq!(map.get(&3), Some(&13));
        assert_eq!(map.get(&5), Some(&15));
        assert_eq!(map.get(&7), None);
    }

    #[test]
    fn entry_smoke() {
        let mut map: VecMap<i32, i32> = VecMap::new();
        *map.entry(5).or_insert(0) += 1;
        map.entry(3).insert(2);
        assert_eq!(map.get(&3), Some(&2));
        assert_eq!(map.get(&5), Some(&1));
    }

    #[test]
    fn iterators() {
        let mut map: VecMap<i32, i32> = VecMap::new();
        map.insert(1, 11);
        map.insert(0, 10);
        map.insert(2, 20);

        assert_eq!(
            map.iter().copied().collect::<Vec<(i32, i32)>>(),
            vec![(0, 10), (1, 11), (2, 20)]
        );

        for v in map.values_mut() {
            *v += 1;
        }
        for (_k, v) in map.iter_mut() {
            *v += 1;
        }

        assert_eq!(map.keys().copied().collect::<Vec<i32>>(), vec![0, 1, 2]);
        assert_eq!(
            map.values().copied().collect::<Vec<i32>>(),
            vec![12, 13, 22]
        );
    }
}
