use std::collections::HashMap;
use std::iter::FromIterator;

use criterion::{
    black_box, criterion_group, criterion_main, Bencher, BenchmarkId, Criterion, Throughput,
};
use rand::{prelude::Distribution, thread_rng};
use vecmap::{BinaryMap, LinearMap};

trait Key: Clone + Eq + Ord {
    fn generate_keys(count: usize) -> Vec<Self>;
}

impl Key for u32 {
    fn generate_keys(count: usize) -> Vec<Self> {
        rand::distributions::Uniform::new(0, (count / 2) as Self)
            .sample_iter(thread_rng())
            .take(count)
            .collect()
    }
}


fn random_string() -> String {
    use rand::distributions::{Alphanumeric, DistString};
    let len = rand::distributions::Uniform::new(4, 20).sample(&mut thread_rng());
    Alphanumeric.sample_string(&mut thread_rng(), len)
}

impl Key for String {
    fn generate_keys(count: usize) -> Vec<Self> {
        (0..count).into_iter().map(|_| random_string()).collect()
    }
}

const SIZES: &[usize] = &[2, 8, 32, 128, 512, 2048, 8192, 32768];

macro_rules! fill_map {
    ($fun_name:ident, $kind:ty, $key:ty) => {
        fn $fun_name(b: &mut Bencher, &size: &usize) {
            let data = <$key as Key>::generate_keys(size);
            b.iter(|| {
                let mut map = <$kind>::new();
                data.iter().cloned().enumerate().for_each(|(i, k)| {
                    map.insert(k, i as u32);
                });
                black_box(map);
            });
        }
    };
}

fill_map!(fill_linear_map_u32, LinearMap::<u32, u32>, u32);
fill_map!(fill_binary_map_u32, BinaryMap::<u32, u32>, u32);
fill_map!(fill_hash_map_u32, HashMap::<u32, u32>, u32);
fill_map!(fill_linear_map_str, LinearMap::<String, u32>, String);
fill_map!(fill_binary_map_str, BinaryMap::<String, u32>, String);
fill_map!(fill_hash_map_str, HashMap::<String, u32>, String);

macro_rules! map_from_iter {
    ($fun_name:ident, $kind:ty, $key:ty) => {
        fn $fun_name(b: &mut Bencher, &size: &usize) {
            let data = <$key as Key>::generate_keys(size);
            b.iter(|| {
                let map = <$kind>::from_iter(
                    data.iter().cloned().enumerate().map(|(i, k)| (k, i as u32)),
                );
                black_box(map);
            });
        }
    };
}

map_from_iter!(linear_map_from_iter_u32, LinearMap::<u32, u32>, u32);
map_from_iter!(binary_map_from_iter_u32, BinaryMap::<u32, u32>, u32);
map_from_iter!(hash_map_from_iter_u32, HashMap::<u32, u32>, u32);
map_from_iter!(linear_map_from_iter_str, LinearMap::<String, u32>, String);
map_from_iter!(binary_map_from_iter_str, BinaryMap::<String, u32>, String);
map_from_iter!(hash_map_from_iter_str, HashMap::<String, u32>, String);

macro_rules! lookup_map {
    ($fun_name:ident, $kind:ty, $key:ty) => {
        fn $fun_name(b: &mut Bencher, &size: &usize) {
            let data = <$key as Key>::generate_keys(size);
            let lookup_data = <$key as Key>::generate_keys(size);
            let mut map = <$kind>::new();
            data.iter().cloned().enumerate().for_each(|(i, k)| {
                map.insert(k, i as u32);
            });
            let mut i = 0;
            b.iter(|| {
                let key = &lookup_data[i % size];
                black_box(map.get(key));
                i = (i + 1) % size;
            })
        }
    };
}

lookup_map!(lookup_linear_map_u32, LinearMap::<u32, u32>, u32);
lookup_map!(lookup_binary_map_u32, BinaryMap::<u32, u32>, u32);
lookup_map!(lookup_hash_map_u32, HashMap::<u32, u32>, u32);
lookup_map!(lookup_linear_map_str, LinearMap::<String, u32>, String);
lookup_map!(lookup_binary_map_str, BinaryMap::<String, u32>, String);
lookup_map!(lookup_hash_map_str, HashMap::<String, u32>, String);

fn bench_fill(c: &mut Criterion) {
    let mut group = c.benchmark_group("fill");
    for size in SIZES {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::new("linear/u32", size), size, fill_linear_map_u32);
        group.bench_with_input(BenchmarkId::new("binary/u32", size), size, fill_binary_map_u32);
        group.bench_with_input(BenchmarkId::new("hash/u32", size), size, fill_hash_map_u32);
        group.bench_with_input(BenchmarkId::new("linear/str", size), size, fill_linear_map_str);
        group.bench_with_input(BenchmarkId::new("binary/str", size), size, fill_binary_map_str);
        group.bench_with_input(BenchmarkId::new("hash/str", size), size, fill_hash_map_str);
    }
    group.finish()
}

fn bench_from_iter(c: &mut Criterion) {
    let mut group = c.benchmark_group("from_iter");
    for size in SIZES {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::new("linear/u32", size), size, linear_map_from_iter_u32);
        group.bench_with_input(BenchmarkId::new("binary/u32", size), size, binary_map_from_iter_u32);
        group.bench_with_input(BenchmarkId::new("hash/u32", size), size, hash_map_from_iter_u32);
        group.bench_with_input(BenchmarkId::new("linear/str", size), size, linear_map_from_iter_str);
        group.bench_with_input(BenchmarkId::new("binary/str", size), size, binary_map_from_iter_str);
        group.bench_with_input(BenchmarkId::new("hash/str", size), size, hash_map_from_iter_str);
    }
    group.finish()
}

fn bench_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("lookup");
    for size in SIZES {
        group.throughput(Throughput::Elements(1));
        group.bench_with_input(BenchmarkId::new("linear/u32", size), size, lookup_linear_map_u32);
        group.bench_with_input(BenchmarkId::new("binary/u32", size), size, lookup_binary_map_u32);
        group.bench_with_input(BenchmarkId::new("hash/u32", size), size, lookup_hash_map_u32);
        group.bench_with_input(BenchmarkId::new("linear/str", size), size, lookup_linear_map_str);
        group.bench_with_input(BenchmarkId::new("binary/str", size), size, lookup_binary_map_str);
        group.bench_with_input(BenchmarkId::new("hash/str", size), size, lookup_hash_map_str);
    }
}

criterion_group!(benches, bench_fill, bench_from_iter, bench_lookup);
criterion_main!(benches);
