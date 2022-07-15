//! <https://adventofcode.com/2019/day/18>
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

type Location = (usize, usize);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    map: HashMap<Location, u8>,
    location: HashMap<u8, Location>,
}

#[aoc(2019, 18)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c as u8).collect::<Vec<u8>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        for (j, v) in self.line.iter().enumerate() {
            for (i, c) in v.iter().enumerate() {
                self.map.insert((j, i), *c);
                if (b'A' <= *c && *c <= b'Z') || (b'a' <= *c && *c <= b'z') {
                    self.location.insert(*c, (j, i));
                }
            }
        }
        // dbg!(self.line.len());
        dbg!(&self.location.len() / 2);
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

impl Puzzle {
    fn distance(&self, from: u8, to: u8, inventy: &[u8]) -> usize {
        0
    }
}
