//! <https://adventofcode.com/2015/day/6>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Clone, Debug, PartialEq)]
enum Code {
    Toggle(usize, usize, usize, usize),
    TurnOff(usize, usize, usize, usize),
    TurnOn(usize, usize, usize, usize),
}

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<Code>,
}

mod parser {
    use {
        super::Code,
        crate::parser::parse_usize,
        winnow::{
            ascii::newline,
            combinator::{alt, separated, seq},
            ModalResult, Parser,
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Code> {
        alt((
            seq!(_: "toggle ", parse_usize, _: ",", parse_usize, _: " through ", parse_usize, _: ",", parse_usize)
                .map(|(x1, y1, x2, y2)| Code::Toggle(x1, y1, x2, y2)),
            seq!(_: "turn off " , parse_usize, _: ",", parse_usize, _: " through ", parse_usize, _: ",", parse_usize)
                .map(|( x1, y1,  x2,  y2)| Code::TurnOff(x1, y1, x2, y2)),
            seq!(_: "turn on " , parse_usize, _: ",", parse_usize, _: " through ", parse_usize, _: ",", parse_usize)
                .map(|( x1, y1,  x2, y2)| Code::TurnOn(x1, y1, x2, y2)),
        )).parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Code>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2015, 6)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parser::parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut lights: [[bool; 1000]; 1000] = [[false; 1000]; 1000];
        for c in self.line.iter() {
            match c {
                Code::Toggle(bj, bi, ej, ei) => {
                    for v in &mut lights[*bj..=*ej] {
                        for l in &mut v[*bi..=*ei] {
                            *l = !*l;
                        }
                    }
                }
                Code::TurnOff(bj, bi, ej, ei) => {
                    for v in &mut lights[*bj..=*ej] {
                        for l in &mut v[*bi..=*ei] {
                            *l = false;
                        }
                    }
                }
                Code::TurnOn(bj, bi, ej, ei) => {
                    for v in &mut lights[*bj..=*ej] {
                        for l in &mut v[*bi..=*ei] {
                            *l = true;
                        }
                    }
                }
            }
        }
        lights
            .iter()
            .map(|v| v.iter().filter(|l| **l).count())
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut lights: [[usize; 1000]; 1000] = [[0; 1000]; 1000];
        for c in self.line.iter() {
            match c {
                Code::Toggle(bj, bi, ej, ei) => {
                    for v in &mut lights[*bj..=*ej] {
                        for l in &mut v[*bi..=*ei] {
                            *l += 2;
                        }
                    }
                }
                Code::TurnOff(bj, bi, ej, ei) => {
                    for v in &mut lights[*bj..=*ej] {
                        for l in &mut v[*bi..=*ei] {
                            *l = if *l == 0 { 0 } else { *l - 1 };
                        }
                    }
                }
                Code::TurnOn(bj, bi, ej, ei) => {
                    for v in &mut lights[*bj..=*ej] {
                        for l in &mut v[*bi..=*ei] {
                            *l += 1;
                        }
                    }
                }
            }
        }
        lights.iter().map(|v| v.iter().sum::<usize>()).sum()
    }
}
