pub mod map;

pub use map::{BinaryMap, LinearMap, Map};

pub trait SearchStrategy {}
pub struct BinarySearch;
impl SearchStrategy for BinarySearch {}
pub struct LinearSearch;
impl SearchStrategy for LinearSearch {}
