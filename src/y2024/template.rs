//! <https://adventofcode.com/2024/day/X>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        parser::parse_usize,
    },
    serde::Serialize,
    std::collections::HashMap,
    winnow::{
        ascii::newline,
        combinator::{repeat, repeat_till, separated, terminated},
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

#[aoc(2024, X)]
impl AdventOfCode for Puzzle {
    // const DELIMITER: &'static str = "\n";
    // fn parse(&mut self, input: String) -> Result<String, ParseError> {
    //     let s = &mut input.as_str();
    //     self.line = parser(s)?;
    //     Self::parsed()
    // }
    // fn insert(&mut self, block: &str) -> Result<(), ParseError> {
    //     dbg!(block);
    //     Ok(())
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
