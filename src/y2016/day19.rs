//! <https://adventofcode.com/2016/day/19>
use std::usize;

use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    line_parser,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    input: usize,
}

#[aoc(2016, 19)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.input = line_parser::to_usize(block)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        // self.input = 5;
        let mut next = vec![0];
        for i in 1..=self.input {
            next.push(i + 1);
        }
        next[self.input] = 1;
        let mut index = 1;
        while next[index] != index {
            let i = next[next[index]];
            next[index] = i;
            index = i;
        }
        index
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
