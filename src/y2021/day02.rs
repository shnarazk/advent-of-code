#![allow(unused_imports)]
#![allow(dead_code)]
use crate::{Description, ParseError, ProblemObject, ProblemSolver};
use lazy_static::lazy_static;
use regex::Regex;
// use std::collections::HashMap;

#[derive(Debug, PartialEq)]
enum Object {
    Forward(usize),
    Down(usize),
    Up(usize),
}

impl ProblemObject for Object {
    fn parse(s: &str) -> Result<Self, ParseError> {
        lazy_static! {
            static ref PARSER: Regex = Regex::new(r"^(forward|down|up) ([0-9]+)").expect("wrong");
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
                Object::Forward(n) => {
                    horizontal += n;
                }
                Object::Down(n) => {
                    depth += n;
                }
                Object::Up(n) => {
                    depth -= n;
                }
            }
        }
        horizontal * depth
    }
    fn part2(&mut self) -> usize {
        let mut horizontal: usize = 0;
        let mut depth: usize = 0;
        let mut aim: usize = 0;
        for l in self.line.iter() {
            match *l {
                Object::Forward(n) => {
                    horizontal += n;
                    depth += aim * n;
                }
                Object::Down(n) => {
                    aim += n;
                }
                Object::Up(n) => {
                    aim -= n;
                }
            }
        }
        horizontal * depth
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}
