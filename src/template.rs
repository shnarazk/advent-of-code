#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::{AdventOfCode, Description, FromDataFile, ParseError};
use lazy_static::lazy_static;
use regex::Regex;
use std::collections::HashMap;

#[derive(Debug, PartialEq)]
struct DataSegment {}

impl FromDataFile for DataSegment {
    /// make a `Object` from a string block
    fn parse(s: &str) -> Result<Self, ParseError> {
        lazy_static! {
            static ref PARSER: Regex = Regex::new(r"^([0-9]+)$").expect("wrong");
        }
        let segment = PARSER.captures(s).ok_or(ParseError)?;
        Err(ParseError)
    }
}

#[derive(Debug, PartialEq)]
struct Puzzle {}

impl AdventOfCode<DataSegment, usize, usize> for Puzzle {
    const YEAR: usize = 2021;
    const DAY: usize = 0;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self {}
    }
    /// add a data block
    fn insert(&mut self, object: DataSegment) {}
    /// solver for part1
    fn part1(&mut self) -> usize {
        0
    }
    /// solver for part2
    fn part2(&mut self) -> usize {
        0
    }
}

impl TryFrom<Description> for Puzzle {
    type Error = ParseError;
    fn try_from(desc: Description) -> Result<Self, ParseError> {
        Puzzle::parse(desc)
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::try_from(desc).expect("failed to parse").run(part));
}

#[cfg(test)]
mod test {
    use {
        super::*,
        crate::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        const TEST1: &str = "0\n1\n2";
        assert_eq!(
            Puzzle::parse(Description::TestData(TEST1.to_string())).expect("-").run(1),
            Answer::Part1(0)
        );
    }
    #[test]
    fn test_part2() {
        const TEST2: &str = "0\n1\n2";
        assert_eq!(
            Puzzle::parse(Description::TestData(TEST2.to_string())).expect("-").run(2),
            Answer::Part2(0)
        );
    }
}
