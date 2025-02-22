//! <https://adventofcode.com/2016/day/08>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Eq, PartialEq)]
enum Op {
    Rect(usize, usize),
    RotateRow(usize, usize),
    RotateCol(usize, usize),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Op>,
}

mod parser {
    use {
        super::Op,
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, separated, seq},
        },
    };

    fn parse_op(s: &mut &str) -> ModalResult<Op> {
        alt((
            seq!(_: "rect ", parse_usize, _: "x", parse_usize).map(|(w, h)| Op::Rect(w, h)),
            seq!(_: "rotate row y=", parse_usize, _: " by ", parse_usize)
                .map(|(y, x)| Op::RotateRow(y, x)),
            seq!(_: "rotate column x=", parse_usize, _:" by ", parse_usize)
                .map(|(x, y)| Op::RotateCol(x, y)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Op>> {
        separated(1.., parse_op, newline).parse_next(s)
    }
}

#[aoc(2016, 8)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = 6;
        let width = 50;
        let mut display = [[false; 50]; 6];
        for op in self.line.iter() {
            match op {
                Op::Rect(w, h) => {
                    for l in display.iter_mut().take(*h) {
                        for p in l.iter_mut().take(*w) {
                            *p = true;
                        }
                    }
                }
                Op::RotateCol(x, d) => {
                    for _ in 0..*d {
                        let tmp = display[height - 1][*x];
                        for j in (1..height).rev() {
                            display[j][*x] = display[j - 1][*x];
                        }
                        display[0][*x] = tmp;
                    }
                }
                Op::RotateRow(y, d) => {
                    for _ in 0..*d {
                        let tmp = display[*y][width - 1];
                        for j in (1..width).rev() {
                            display[*y][j] = display[*y][j - 1];
                        }
                        display[*y][0] = tmp;
                    }
                }
            }
        }
        display
            .iter()
            .map(|l| l.iter().filter(|b| **b).count())
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let height = 6;
        let width = 50;
        let mut display = [[false; 50]; 6];
        for op in self.line.iter() {
            match op {
                Op::Rect(w, h) => {
                    for l in display.iter_mut().take(*h) {
                        for p in l.iter_mut().take(*w) {
                            *p = true;
                        }
                    }
                }
                Op::RotateCol(x, d) => {
                    for _ in 0..*d {
                        let tmp = display[height - 1][*x];
                        for j in (1..height).rev() {
                            display[j][*x] = display[j - 1][*x];
                        }
                        display[0][*x] = tmp;
                    }
                }
                Op::RotateRow(y, d) => {
                    for _ in 0..*d {
                        let tmp = display[*y][width - 1];
                        for j in (1..width).rev() {
                            display[*y][j] = display[*y][j - 1];
                        }
                        display[*y][0] = tmp;
                    }
                }
            }
        }
        for l in display.iter() {
            for c in l.iter() {
                print!("{}", if *c { '#' } else { ' ' });
            }
            println!();
        }
        0
    }
}
