pub mod vecmap;
pub use vecmap::VecMap;

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
}
