extern crate rand;
extern crate vecmap;

use criterion::{
    black_box, criterion_group, criterion_main, Bencher, BenchmarkId, Criterion, Throughput,
};
use rand::prelude::*;
use std::collections::HashMap;
use vecmap::VecMap;

fn bench_fill_vecmap(b: &mut Bencher, &size: &i32) {
    let numbers: Vec<i32> = rand::distributions::Uniform::new(0, size)
        .sample_iter(thread_rng())
        .take(size as usize)
        .collect();
    b.iter(|| {
        let mut map: VecMap<i32, i32> = VecMap::new();
        for i in 0..size {
            map.insert(numbers[i as usize], i);
        }
        black_box(map.get(&0));
    });
}

fn bench_fill_hashmap(b: &mut Bencher, &size: &i32) {
    let numbers: Vec<i32> = rand::distributions::Uniform::new(0, size)
        .sample_iter(thread_rng())
        .take(size as usize)
        .collect();
    b.iter(|| {
        let mut map: HashMap<i32, i32> = HashMap::new();
        for i in 0..size {
            map.insert(numbers[i as usize], i);
        }
        black_box(map.get(&0));
    });
}

fn bench_fill(c: &mut Criterion) {
    let mut group = c.benchmark_group("Fill");
    for size in [1, 10, 100, 1000, 10000].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::new("VecMap", size), size, bench_fill_vecmap);
        group.bench_with_input(BenchmarkId::new("HashMap", size), size, bench_fill_hashmap);
    }
    group.finish();
}

fn bench_entry_vecmap(b: &mut Bencher, &size: &i32) {
    let mut map: VecMap<i32, i32> = VecMap::new();
    let mut rng = thread_rng();
    let distr = rand::distributions::Uniform::new(0, size);
    for i in 0..size {
        map.insert(distr.sample(&mut rng), i);
    }
    b.iter(|| {
        black_box(map.entry(distr.sample(&mut rng)));
    });
}

fn bench_entry_hashmap(b: &mut Bencher, &size: &i32) {
    let mut map: HashMap<i32, i32> = HashMap::new();
    let mut rng = thread_rng();
    let distr = rand::distributions::Uniform::new(0, size);
    for i in 0..size {
        map.insert(distr.sample(&mut rng), i);
    }
    b.iter(|| {
        black_box(map.entry(distr.sample(&mut rng)));
    });
}

fn bench_entry(c: &mut Criterion) {
    let mut group = c.benchmark_group("Entry");
    for size in [1, 10, 100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("VecMap", size), size, bench_entry_vecmap);
        group.bench_with_input(BenchmarkId::new("HashMap", size), size, bench_entry_hashmap);
    }
    group.finish();
}

fn bench_counting_vecmap(b: &mut Bencher, &size: &i32) {
    let mut map: VecMap<i32, i32> = VecMap::new();
    let mut rng = thread_rng();
    let distr = rand::distributions::Uniform::new(0, size);
    b.iter(|| {
        *map.entry(distr.sample(&mut rng)).or_insert(0) += 1;
    });
    black_box(map);
}

fn bench_counting_hashmap(b: &mut Bencher, &size: &i32) {
    let mut map: HashMap<i32, i32> = HashMap::new();
    let mut rng = thread_rng();
    let distr = rand::distributions::Uniform::new(0, size);
    b.iter(|| {
        *map.entry(distr.sample(&mut rng)).or_insert(0) += 1;
    });
    black_box(map);
}

fn bench_counting(c: &mut Criterion) {
    let mut group = c.benchmark_group("Counting");
    for size in [1, 10, 100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("VecMap", size),
            size,
            bench_counting_vecmap,
        );
        group.bench_with_input(
            BenchmarkId::new("HashMap", size),
            size,
            bench_counting_hashmap,
        );
    }
    group.finish();
}

criterion_group!(benches, bench_fill, bench_entry, bench_counting);
criterion_main!(benches);
