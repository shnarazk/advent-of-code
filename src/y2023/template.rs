//! <https://adventofcode.com/2023/day/0>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        parser,
    },
    serde::Serialize,
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<()>,
}

// impl Default for Puzzle {
//     fn default() -> Self {
//         Puzzle { }
//     }
// }

#[aoc(2023, 0)]
impl AdventOfCode for Puzzle {
    // const DELIMITER: &'static str = "\n";
    // fn header(&mut self, input: String) -> Result<String, ParseError> {
    //     Ok("".to_string())
    // }
    // fn insert(&mut self, block: &str) -> Result<(), ParseError> {
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
