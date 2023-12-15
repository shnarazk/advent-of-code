//! <https://adventofcode.com/2023/day/15>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<String>,
}

// impl Default for Puzzle {
//     fn default() -> Self {
//         Puzzle { }
//     }
// }

#[aoc(2023, 15)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block
            .trim()
            .split(',')
            .map(|s| s.to_string())
            .collect::<Vec<_>>();
        Ok(())
    }
    fn end_of_data(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|s| {
                s.bytes()
                    .fold(0usize, |ac, x| (17 * (ac + x as usize)) % 256)
            })
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
