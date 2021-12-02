#![allow(unused_imports)]
#![allow(dead_code)]
use crate::{Description, ParseError, ProblemObject, ProblemSolver};
use lazy_static::lazy_static;
use regex::Regex;
// use std::collections::HashMap;

pub fn go(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

#[derive(Debug, PartialEq)]
enum Object {
    Forward(usize),
    Down(usize),
    Up(usize),
}

impl ProblemObject for Object {
    fn parse(s: &str) -> Result<Self, ParseError> {
        lazy_static! {
            static ref PARSER: Regex =
                Regex::new(r"^(forward|down|up) ([0-9]+)").expect("wrong");
        }
        let segment = PARSER.captures(s).ok_or(ParseError)?;
        let num = segment[2].parse::<usize>()?;
        match &segment[1] {
            "forward" => Ok(Object::Forward(num)),
            "down" => Ok(Object::Down(num)),
            "up" => Ok(Object::Up(num)),
            _ => Err(ParseError),
        }
    }
}

#[derive(Debug, PartialEq)]
struct Setting {
    line: Vec<Object>,
}

impl ProblemSolver<Object, usize, usize> for Setting {
    const YEAR: usize = 2021;
    const DAY: usize = 2;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Setting { line: Vec::new() }
    }
    fn insert(&mut self, object: Object) {
        self.line.push(object)
    }
    fn part1(&mut self) -> usize {
        let mut horizontal: usize = 0;
        let mut depth: usize = 0;
        for l in self.line.iter() {
            match *l {
                Object::Forward(n) => { horizontal += n; },
                Object::Down(n) => { depth += n; },
                Object::Up(n) => { depth -= n; },
            }
        }
        dbg!(horizontal, depth);
        horizontal * depth
    }
    fn part2(&mut self) -> usize {
        let mut horizontal: usize = 0;
        let mut depth: usize = 0;
        let mut aim: usize = 0; 
        for l in self.line.iter() {
            match *l {
                Object::Forward(n) => { horizontal += n; depth += aim * n; },
                Object::Down(n) => { aim += n; },
                Object::Up(n) => { aim -= n; },
            }
        }
        dbg!(horizontal, depth);
        horizontal * depth
    }
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
