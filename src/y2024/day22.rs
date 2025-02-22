//! <https://adventofcode.com/2024/day/22>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser::parse_usize,
    },
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{
        collections::{HashMap, HashSet},
        hash::BuildHasherDefault,
    },
    winnow::{ModalResult, Parser, ascii::newline, combinator::separated},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<usize>,
    threshold: usize,
}

fn parse(s: &mut &str) -> ModalResult<Vec<usize>> {
    separated(1.., parse_usize, newline).parse_next(s)
}

#[aoc(2024, 22)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parse(&mut input)?;
        self.threshold = self.get_config().alt.as_ref().map_or(2000, |_| 2000);
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|seed| generate(*seed, self.threshold))
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        let matrix = self
            .line
            .par_iter()
            .map(|secret| {
                sequence(*secret, self.threshold)
                    .iter()
                    .map(|n| n % 10)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let trends = matrix
            .par_iter()
            .map(|seq| {
                let mut hash: FxHashMap<[isize; 4], usize> =
                    HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
                for v in seq.windows(5) {
                    let diffs = v
                        .windows(2)
                        .map(|s| s[1] as isize - s[0] as isize)
                        .collect::<Vec<isize>>();
                    let profit = *v.last().unwrap();
                    let trend = [diffs[0], diffs[1], diffs[2], diffs[3]];
                    hash.entry(trend).or_insert(profit);
                }
                hash
            })
            .collect::<Vec<_>>();
        let all_trends = trends.iter().fold(
            HashSet::<_, BuildHasherDefault<FxHasher>>::default(),
            |acc, hash| {
                hash.keys().fold(acc, |mut acc, trend| {
                    acc.insert(*trend);
                    acc
                })
            },
        );
        all_trends
            .par_iter()
            .map(|trend| {
                trends
                    .iter()
                    .map(|hash| hash.get(trend).map_or(0, |n| *n))
                    .sum::<usize>()
            })
            .max()
            .unwrap()
    }
}

fn next(seed: usize) -> usize {
    let s1 = ((seed * 64) ^ seed) % 16777216;
    let s2 = ((s1 / 32) ^ s1) % 16777216;
    ((s2 * 2048) ^ s2) % 16777216
}

fn generate(seed: usize, limit: usize) -> usize {
    (0..limit).fold(seed, |n, _| next(n))
}

fn sequence(seed: usize, limit: usize) -> Vec<usize> {
    let mut v = Vec::with_capacity(limit + 1);
    let mut n = seed;
    v.push(n);
    for _ in 0..limit {
        n = next(n);
        v.push(n);
    }
    v
}
