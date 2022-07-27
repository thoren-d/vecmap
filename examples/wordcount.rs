use std::collections::HashMap;
use vecmap::{BinaryMap, LinearMap};

fn count_words_linear_map(words: &[&str]) {
    let before = std::time::Instant::now();

    let mut map: LinearMap<&str, usize> = LinearMap::new();
    for word in words {
        *map.entry(*word).or_default() += 1;
    }
    let (word, count) = map
        .iter()
        .max_by_key(|(_k, v)| **v)
        .expect("should've been a word in here");

    let elapsed = before.elapsed().as_secs_f64();
    println!("***LinearMap***");
    println!("Words: {}", words.len());
    println!("Unique Words: {}", map.len());
    println!("Most Common: {} ({})", *word, *count);
    println!("Elapsed: {}", elapsed);
    println!("Words/s: {}", words.len() as f64 / elapsed);
}

fn count_words_binary_map(words: &[&str]) {
    let before = std::time::Instant::now();

    let mut map: BinaryMap<&str, usize> = BinaryMap::new();
    for word in words {
        *map.entry(*word).or_default() += 1;
    }
    let (word, count) = map
        .iter()
        .max_by_key(|(_k, v)| **v)
        .expect("should've been a word in here");

    let elapsed = before.elapsed().as_secs_f64();
    println!("***BinaryMap***");
    println!("Words: {}", words.len());
    println!("Unique Words: {}", map.len());
    println!("Most Common: {} ({})", *word, *count);
    println!("Elapsed: {}", elapsed);
    println!("Words/s: {}", words.len() as f64 / elapsed);
}

fn count_words_hash_map(words: &[&str]) {
    let before = std::time::Instant::now();

    let mut map: HashMap<&str, usize> = HashMap::new();
    for word in words {
        *map.entry(*word).or_default() += 1;
    }
    let (word, count) = map
        .iter()
        .max_by_key(|(_k, v)| **v)
        .expect("should've been a word in here");

    let elapsed = before.elapsed().as_secs_f64();
    println!("***HashMap***");
    println!("Words: {}", words.len());
    println!("Unique Words: {}", map.len());
    println!("Most Common: {} ({})", *word, *count);
    println!("Elapsed: {}", elapsed);
    println!("Words/s: {}", words.len() as f64 / elapsed);
}

fn main() {
    let file = std::env::args()
        .nth(1)
        .expect("expected usage: wordcount <text file>");
    let file = std::fs::read(file).expect("failed to read file");
    let file = String::from_utf8(file).expect("file contained invalid utf-8");
    let words: Vec<&str> = file.split_whitespace().collect();

    count_words_linear_map(&words);
    println!();
    count_words_binary_map(&words);
    println!();
    count_words_hash_map(&words);
}
