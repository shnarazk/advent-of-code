//! <https://adventofcode.com/2017/day/6>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{HashMap, HashSet},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<usize>,
    len: usize,
}

#[aoc(2017, 6)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = line_parser::to_usizes(block, '\n')?;
        Ok(())
    }
    fn after_insert(&mut self) {
        self.len = self.line.len();
        dbg!(self.len);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut visited: HashSet<Vec<usize>> = HashSet::new();
        for step in 1_usize.. {
            let mut target = 0;
            let mut nblocks = 0;
            for (i, nb) in self.line.iter().enumerate() {
                if nblocks < *nb {
                    target = i;
                    nblocks = *nb;
                }
            }
            self.line[target] = 0;
            for n in 0..nblocks {
                self.line[(target + n + 1) % self.len] += 1;
            }
            if visited.contains(&self.line) {
                return step;
            }
            visited.insert(self.line.clone());
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
