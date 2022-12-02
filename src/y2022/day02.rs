//! <https://adventofcode.com/2022/day/2>
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
    line: Vec<(char, char)>,
}

#[aoc(2022, 2)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let chars = block.chars().collect::<Vec<_>>();
        self.line.push((chars[0], chars[2]));
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        #[allow(clippy::identity_op)]
        self.line
            .iter()
            .map(|game| match game {
                ('A', 'X') => 1 + 3,
                ('A', 'Y') => 2 + 6,
                ('A', 'Z') => 3 + 0,
                ('B', 'X') => 1 + 0,
                ('B', 'Y') => 2 + 3,
                ('B', 'Z') => 3 + 6,
                ('C', 'X') => 1 + 6,
                ('C', 'Y') => 2 + 0,
                ('C', 'Z') => 3 + 3,
                _ => unreachable!(),
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
