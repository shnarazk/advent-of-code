//! <https://adventofcode.com/2016/day/07>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    md5::{Digest, Md5},
    std::{collections::HashMap, process::Command},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<()>,
}

#[aoc(2016, 7)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        if let Ok(output) = Command::new("bqn/2016/day07.bqn").output() {
            println!("{}", String::from_utf8_lossy(&output.stdout));
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
