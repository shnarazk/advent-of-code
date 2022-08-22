//! <https://adventofcode.com/2018/day/8>
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
    line: Vec<usize>,
}

#[aoc(2018, 8)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = line_parser::to_usizes(block, ' ')?;
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        self.build_span(0).1
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

impl Puzzle {
    /// return:
    /// - the index of the next entry
    /// - and the sum of metadatas in this range
    fn build_span(&self, index: usize) -> (usize, usize) {
        let num_children = self.line[index];
        let num_metadata = self.line[index + 1];
        let mut sum_metas = 0;
        let mut i = index + 2;
        for _ in 0..num_children {
            let tmp = self.build_span(i);
            i = tmp.0;
            sum_metas += tmp.1;
        }
        for m in 0..num_metadata {
            sum_metas += self.line[i + m];
        }
        (i + num_metadata, sum_metas)
    }
}
