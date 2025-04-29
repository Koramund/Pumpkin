use clap::ValueEnum;
use rand::prelude::{SliceRandom, StdRng};
use rand::SeedableRng;
use crate::pumpkin_assert_simple;

#[derive(Debug, PartialEq, Eq, ValueEnum,  Copy, Clone)]
pub enum Shuffle {
    None,
    Scalar,
    Random,
}

impl Default for Shuffle {
    fn default() -> Self {
        Shuffle::None
    }
}

pub fn random_shuffle<T: Clone>(arr: &Box<[T]>, seed: u64) -> Box<[T]> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut new_arr: Vec<T> = arr.to_vec();
    new_arr.shuffle(&mut rng);
    new_arr.into_boxed_slice()
}

pub fn proxy_sort<T: Clone>(arr: &Box<[T]>, keys: &Box<[i32]>) -> Box<[T]> {
    pumpkin_assert_simple!(arr.len() == keys.len(), "Sorting by proxy requires equal lengths");

    let mut paired: Vec<(T, i32)> = arr.iter().cloned().zip(keys.iter().cloned()).collect();
    paired.sort_by_key(|&(_, key)| key);
    paired.into_iter().map(|(val, _)| val).collect::<Vec<_>>().into_boxed_slice()
}

#[derive(Debug, PartialEq, Eq, ValueEnum,  Copy, Clone)]
pub enum LinearInequalityType {
    Incremental,
    Sequential,
    Totalizer,
}

impl Default for LinearInequalityType {
    fn default() -> Self {
        LinearInequalityType::Incremental
    }
}