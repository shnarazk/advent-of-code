//! <https://adventofcode.com/2018/day/5>
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
    line: Vec<u8>,
}

#[aoc(2018, 5)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block.chars().map(|c| c as u8).collect::<Vec<u8>>();
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let dist = b'a' - b'A';
        let mut updated = true;
        while updated {
            updated = false;
            let mut index = 0;
            for i in 0..self.line.len() - 1 {
                if self.line[i] + dist == self.line[i + 1]
                    || self.line[i] == self.line[i + 1] + dist
                {
                    index = i;
                    updated = true;
                    break;
                }
            }
            if updated {
                self.line.remove(index);
                self.line.remove(index);
                // dbg!(self.line.iter().map(|c| *c as char).collect::<String>());
            }
        }
        self.line.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
