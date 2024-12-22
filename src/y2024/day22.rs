//! <https://adventofcode.com/2024/day/22>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        parser::parse_usize,
    },
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap, HashSet},
        hash::BuildHasherDefault,
    },
    winnow::{
        ascii::newline,
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<usize>,
    threshold: usize,
}

fn parse(s: &mut &str) -> PResult<Vec<usize>> {
    separated(1.., parse_usize, newline).parse_next(s)
}

#[aoc(2024, 22)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        // let mut secret = 123;
        // dbg!(next(&mut secret));
        // dbg!(next(&mut secret));
        // dbg!(next(&mut secret));
        // dbg!(next(&mut secret));
        // dbg!(next(&mut secret));
        // dbg!(next(&mut secret));
        self.threshold = self.get_config().alt.as_ref().map_or(2000, |_| 2000);
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
            .iter()
            .map(|secret| {
                sequence(*secret, self.threshold)
                    .iter()
                    .map(|n| n % 10)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let trends = matrix
            .iter()
            .map(|seq| {
                let mut hash: HashMap<[isize; 4], usize> = HashMap::new();
                for v in seq.windows(5) {
                    let diffs = v
                        .windows(2)
                        .map(|s| s[1] as isize - s[0] as isize)
                        .collect::<Vec<isize>>();
                    if diffs == [-2, 1, -1, 3] {
                        dbg!();
                    }
                    let profit = *v.last().unwrap();
                    let trend = [diffs[0], diffs[1], diffs[2], diffs[3]];
                    if hash.get(&trend).is_none() {
                        hash.insert(trend, profit);
                    }
                }
                hash
            })
            .collect::<Vec<_>>();
        let all_trends = trends.iter().fold(HashSet::new(), |acc, hash| {
            hash.keys().fold(acc, |mut acc, trend| {
                acc.insert(*trend);
                acc
            })
        });
        all_trends
            .iter()
            .map(|trend| {
                if trend == &[-2, 1, -1, 3] {
                    trends
                        .iter()
                        .map(|hash| hash.get(trend).map_or(0, |n| *n))
                        .map(|k| dbg!(k))
                        .sum::<usize>()
                } else {
                    trends
                        .iter()
                        .map(|hash| hash.get(trend).map_or(0, |n| *n))
                        .sum::<usize>()
                }
            })
            .max()
            .unwrap()
    }
}

fn mix(seed: &mut usize, value: usize) {
    let ret = *seed ^ value;
    *seed = ret;
}

fn prune(seed: &mut usize) {
    let ret = *seed % 16777216;
    *seed = ret;
}
fn next(secret: &mut usize) -> usize {
    let s1 = *secret * 64;
    mix(secret, s1);
    prune(secret);
    let s2 = *secret / 32;
    mix(secret, s2);
    prune(secret);
    let s3 = *secret * 2048;
    mix(secret, s3);
    prune(secret);
    *secret
}

fn generate(seed: usize, limit: usize) -> usize {
    (0..limit).fold(seed, |mut n, _| next(&mut n))
}
fn sequence(seed: usize, limit: usize) -> Vec<usize> {
    (0..limit).fold(vec![seed], |mut v, _| {
        let mut n = *v.last().unwrap();
        v.push(next(&mut n));
        v
    })
}
