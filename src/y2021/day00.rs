#![allow(unused_imports)]
use crate::{AdventOfCode, Description, FromDataFile, ParseError};
// use std::collections::HashMap;

#[derive(Debug, PartialEq)]
struct Object {}

impl FromDataFile for Object {
    fn parse(_s: &str) -> Result<Self, ParseError> {
        Err(ParseError)
    }
}

#[derive(Debug, PartialEq)]
struct Setting {}

impl AdventOfCode for Setting {
    type Segment = Object;
    type Output1 = usize;
    type Output2 = usize;
    const YEAR: usize = 2021;
    const DAY: usize = 0;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Setting {}
    }
    // fn input_filename(_desc: Description) -> Option<String> { None }
    fn insert(&mut self, _object: Object) {}
    fn part1(&mut self) -> usize {
        0
    }
    fn part2(&mut self) -> usize {
        0
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).expect("-").run(part));
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
            Setting::parse(Description::TestData(TEST1.to_string()))
                .expect("-")
                .run(1),
            Answer::Part1(0)
        );
    }
    #[test]
    fn test_part2() {
        const TEST2: &str = "0\n1\n2";
        assert_eq!(
            Setting::parse(Description::TestData(TEST2.to_string()))
                .expect("-")
                .run(2),
            Answer::Part2(0)
        );
    }
}
