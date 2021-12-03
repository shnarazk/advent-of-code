#![allow(unused_imports)]
#![allow(dead_code)]
use crate::{Description, ParseError, ProblemObject, ProblemSolver};
use lazy_static::lazy_static;
use regex::Regex;
// use std::collections::HashMap;

#[derive(Debug, PartialEq)]
struct Object {}

impl ProblemObject for Object {
    /// make a `Object` from a string block
    fn parse(s: &str) -> Result<Self, ParseError> {
        lazy_static! {
            static ref PARSER: Regex = Regex::new(r"^").expect("wrong");
        }
        let _segment = PARSER.captures(s).ok_or(ParseError)?;
        Err(ParseError)
    }
}

#[derive(Debug, PartialEq)]
struct Setting {}

impl ProblemSolver<Object, usize, usize> for Setting {
    const YEAR: usize = 2021;
    const DAY: usize = 0;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self {}
    }
    /// add a data block
    fn insert(&mut self, _object: Object) {}
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
    dbg!(Setting::parse(desc).run(part));
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
            Setting::parse(Description::TestData(TEST1.to_string())).run(1),
            Answer::Part1(0)
        );
    }
    #[test]
    fn test_part2() {
        const TEST2: &str = "0\n1\n2";
        assert_eq!(
            Setting::parse(Description::TestData(TEST2.to_string())).run(2),
            Answer::Part2(0)
        );
    }
}
