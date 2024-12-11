//! <https://adventofcode.com/2024/day/13>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        parser,
    },
    rayon::prelude::*,
    serde::Serialize,
    std::collections::HashMap,
    winnow::{
        ascii::newline,
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<()>,
}

// impl Default for Puzzle {
//     fn default() -> Self {
//         Puzzle { }
//     }
// }

// fn parse(str: &mut &str) -> PResult<()> {}

#[aoc(2024, 13)]
impl AdventOfCode for Puzzle {
    // fn parse(&mut self, input: String) -> Result<String, ParseError> {
    //     let s = &mut input.as_str();
    //     self.line = parse(s)?;
    //     Self::parsed()
    // }
    fn end_of_data(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        1
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
