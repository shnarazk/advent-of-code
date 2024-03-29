//! <https://adventofcode.com/2021/day/2>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

#[derive(Debug, PartialEq)]
enum Direction {
    Forward(usize),
    Down(usize),
    Up(usize),
}

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<Direction>,
}

#[aoc(2021, 2)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^(forward|down|up) ([0-9]+)");
        let segment = parser.captures(block).ok_or(ParseError)?;
        let num = segment[2].parse::<usize>()?;
        let object = match &segment[1] {
            "forward" => Direction::Forward(num),
            "down" => Direction::Down(num),
            "up" => Direction::Up(num),
            _ => return Err(ParseError),
        };
        self.line.push(object);
        Ok(())
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
