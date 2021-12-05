#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::{AdventOfCode, Description, TryParse, ParseError};
use lazy_static::lazy_static;
use regex::Regex;
// use std::collections::HashMap;

#[derive(Debug, PartialEq)]
struct DataSegment {}

impl TryParse for DataSegment {
    fn parse(s: &str) -> Result<Self, ParseError> {
        lazy_static! {
            static ref PARSER: Regex = Regex::new(r"^").expect("wrong");
        }
        let segment = PARSER.captures(s).ok_or(ParseError)?;
        Err(ParseError)
    }
}

#[derive(Debug, PartialEq)]
struct Puzzle {}

impl AdventOfCode for Puzzle {
    type Segment = DataSegment;
    type Output1 = usize;
    type Output2 = usize;
    const YEAR: usize = 2021;
    const DAY: usize = 8;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self {}
    }
    fn insert(&mut self, object: Self::Segment) {}
    fn part1(&mut self) -> usize {
        0
    }
    fn part2(&mut self) -> usize {
        0
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::parse(desc).expect("-").run(part));
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
            Puzzle::parse(Description::TestData(TEST1.to_string()))
                .expect("-")
                .run(1),
            Answer::Part1(0)
        );
    }
}
