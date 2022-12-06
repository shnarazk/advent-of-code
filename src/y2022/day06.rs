//! <https://adventofcode.com/2022/day/6>
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
    line: Vec<Vec<char>>,
}

#[aoc(2022, 6)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.chars().collect::<Vec<char>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|l| {
                let mut index = 0;
                for (i, chank) in l.windows(4).enumerate() {
                    if !chank[1..4].contains(&chank[0])
                        && !chank[2..4].contains(&chank[1])
                        && !chank[3..4].contains(&chank[2])
                    {
                        index = i + 4;
                        break;
                    }
                }
                index
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
