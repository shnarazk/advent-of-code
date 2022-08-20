//! <https://adventofcode.com/2018/day/2>
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
    line: Vec<Vec<u8>>,
}

#[aoc(2018, 2)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c as u8).collect::<Vec<_>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut twice: usize = 0;
        let mut thrice: usize = 0;
        for w in self.line.iter() {
            let mut count: HashMap<u8, usize> = HashMap::new();
            for c in w.iter() {
                *count.entry(*c).or_insert(0) += 1;
            }
            twice += count.values().any(|c| *c == 2) as usize;
            thrice += count.values().any(|c| *c == 3) as usize;
        }
        twice * thrice
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
