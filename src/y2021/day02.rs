//! <https://adventofcode.com/2021/day/2>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser::parse_usize,
    },
    winnow::{
        ascii::newline,
        combinator::{alt, separated, seq},
        ModalResult, Parser,
    },
};

#[derive(Clone, Debug, PartialEq)]
enum Direction {
    Forward(usize),
    Down(usize),
    Up(usize),
}

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<Direction>,
}
fn parse_line(s: &mut &str) -> ModalResult<Direction> {
    alt((
        seq!(_: "forward ", parse_usize).map(|(n,)| Direction::Forward(n)),
        seq!(_: "up ", parse_usize).map(|(n,)| Direction::Up(n)),
        seq!(_: "down ", parse_usize).map(|(n,)| Direction::Down(n)),
    ))
    .parse_next(s)
}

fn parse(s: &mut &str) -> ModalResult<Vec<Direction>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc(2021, 2)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(&mut input.as_str())?;
        Self::parsed()
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
