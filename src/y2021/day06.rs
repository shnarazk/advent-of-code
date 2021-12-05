#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::{AdventOfCode, Description, Maybe, ParseError, TryParse};
use lazy_static::lazy_static;
use regex::Regex;
use std::collections::HashMap;

#[derive(Debug, PartialEq)]
struct DataSegment {}

impl TryParse for DataSegment {
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

impl AdventOfCode for Puzzle {
    type Segment = DataSegment;
    type Output1 = usize;
    type Output2 = usize;
    const YEAR: usize = 2021;
    const DAY: usize = 6;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self {}
    }
    // handle header
    // fn header(&mut self, input: &str) -> Maybe<Option<String>> {
    //     let parser: Regex = Regex::new(r"^(.+)\n\n((.|\n)+)$").expect("wrong");
    //     let segment = parser.captures(input).ok_or(ParseError)?;
    //     for num in segment[1].split(',') {
    //         let _value = num.parse::<usize>()?;
    //     }
    //     Ok(Some(segment[2].to_string()))
    // }
    /// add a data block
    fn insert(&mut self, object: Self::Segment) {
        // self = object;
    }
    // finalize
    // fn after_insert(&mut self) {}
    /// solver for part1
    fn part1(&mut self) -> usize {
        0
    }
    /// solver for part2
    fn part2(&mut self) -> usize {
        0
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::solve(&desc, part));
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
            Puzzle::parse(&Description::TestData(TEST1.to_string()))
                .expect("-")
                .run(1),
            Answer::Part1(0)
        );
    }
}
