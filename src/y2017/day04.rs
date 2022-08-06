//! <https://adventofcode.com/2017/day/4>
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

#[aoc(2017, 4)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c as u8).collect::<Vec<u8>>());
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().filter(|p| is_valid(p)).count()
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

fn is_valid(phrase: &[u8]) -> bool {
    let mut words: HashMap<Vec<u8>, usize> = HashMap::new();
    let mut buffer: Vec<u8> = Vec::new();
    for c in phrase.iter() {
        if *c == b' ' {
            *words.entry(buffer).or_insert(0) += 1;
            buffer = Vec::new();
        } else {
            buffer.push(*c);
        }
    }
    if !buffer.is_empty() {
        *words.entry(buffer).or_insert(0) += 1;
    }
    *words.values().max().unwrap_or(&0) < 2
}
