//! <https://adventofcode.com/2017/day/17>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: usize,
}

#[aoc(2017, 17)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block.parse::<usize>()?;
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let step = self.line;
        let mut ring: Vec<usize> = vec![0];
        let mut pos = 0;
        for i in 1..=2017 {
            pos = (step + pos) % ring.len();
            if pos == ring.len() - 1 {
                ring.push(i);
                pos = ring.len() - 1;
            } else {
                ring.insert(pos + 1, i);
                pos += 1;
            }
        }
        ring[(pos + 1) % ring.len()]
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
