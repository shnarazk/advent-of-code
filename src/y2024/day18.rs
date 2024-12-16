//! <https://adventofcode.com/2024/day/18>
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
    std::{collections::HashMap, hash::BuildHasherDefault},
    winnow::{
        ascii::newline,
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<()>,
}

// fn parse(s: &mut &str) -> PResult<()> {}

#[aoc(2024, 18)]
impl AdventOfCode for Puzzle {
    // fn parse(&mut self, input: String) -> Result<String, ParseError> {
    //     self.line = parser(&mut input.as_str())?;
    //     Self::parsed()
    // }
    fn end_of_data(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        // let mut ret: FxHashMap<usize, usize> = HashMap::<usize, usize, BuildHasherDefault<FxHasher>>::default();
        1
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}