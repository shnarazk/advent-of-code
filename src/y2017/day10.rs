//! <https://adventofcode.com/2017/day/10>
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

#[aoc(2017, 10)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = line_parser::to_usizes(block, ',')?;
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let m: usize = 256;
        let mut list = (0..m).collect::<Vec<_>>();
        let mut current_position = 0;
        for (skip_size, length) in self.line.iter().enumerate() {
            assert!(*length <= m);
            for j in 0..length / 2 {
                // println!(
                //     "length: {length}, swap: {} and {}",
                //     (current_position + j) % m,
                //     (current_position + length - j - 1) % m
                // );
                list.swap(
                    (current_position + j) % m,
                    (current_position + length - j - 1) % m,
                );
                assert_ne!(
                    (current_position + j) % m,
                    (current_position + length - j - 1) % m,
                );
            }
            current_position += length + skip_size;
            current_position %= m;
            // println!("{list:?}");
        }
        list[0] * list[1]
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
