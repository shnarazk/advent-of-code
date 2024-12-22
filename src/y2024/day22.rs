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
        collections::{BinaryHeap, HashMap},
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
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|seed| generate(*seed, 2000))
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
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
