//! <https://adventofcode.com/2018/day/1>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
}

#[aoc_at(2018, 1)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = usize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(line_parser::to_isize(block)?);
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().copied().sum::<isize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
