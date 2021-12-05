#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::{AdventOfCode, Description, TryParse, ParseError};
use lazy_static::lazy_static;
use regex::Regex;

#[derive(Debug, PartialEq)]
enum Direction {
    Forward(usize),
    Down(usize),
    Up(usize),
}

impl TryParse for Direction {
    fn parse(s: &str) -> Result<Self, ParseError> {
        lazy_static! {
            static ref PARSER: Regex = Regex::new(r"^(forward|down|up) ([0-9]+)").expect("wrong");
        }
        let segment = PARSER.captures(s).ok_or(ParseError)?;
        let num = segment[2].parse::<usize>()?;
        match &segment[1] {
            "forward" => Ok(Direction::Forward(num)),
            "down" => Ok(Direction::Down(num)),
            "up" => Ok(Direction::Up(num)),
            _ => Err(ParseError),
        }
    }
}

#[derive(Debug, PartialEq)]
struct Puzzle {
    line: Vec<Direction>,
}

impl AdventOfCode for Puzzle {
    type Segment = Direction;
    type Output1 = usize;
    type Output2 = usize;
    const YEAR: usize = 2021;
    const DAY: usize = 2;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self { line: Vec::new() }
    }
    fn insert(&mut self, object: Direction) {
        self.line.push(object)
    }
    fn part1(&mut self) -> usize {
        let mut horizontal: usize = 0;
        let mut depth: usize = 0;
        for l in self.line.iter() {
            match *l {
                Direction::Forward(n) => {
                    horizontal += n;
                }
                Direction::Down(n) => {
                    depth += n;
                }
                Direction::Up(n) => {
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
                Direction::Forward(n) => {
                    horizontal += n;
                    depth += aim * n;
                }
                Direction::Down(n) => {
                    aim += n;
                }
                Direction::Up(n) => {
                    aim -= n;
                }
            }
        }
        horizontal * depth
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::parse(desc).expect("-").run(part));
}
