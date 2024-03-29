#![allow(unused_imports)]
#![allow(dead_code)]
use crate::y2020::traits::{Description, ProblemObject, ProblemSolver};
// use crate::regex;
// use std::collections::HashMap;

pub fn go(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

#[derive(Debug, PartialEq)]
struct Object {}

impl ProblemObject for Object {
    fn parse(_s: &str) -> Option<Self> {
        None
    }
}

#[derive(Debug, PartialEq)]
struct Setting {}

impl ProblemSolver<Object, usize, usize> for Setting {
    const YEAR: usize = 2021;
    const DAY: usize = 0;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Setting {}
    }
    fn insert(&mut self, _object: Object) {}
    fn part1(&mut self) -> usize {
        0
    }
    fn part2(&mut self) -> usize {
        0
    }
}

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::y2020::traits::{Answer, Description},
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
