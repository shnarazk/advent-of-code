//! <https://adventofcode.com/2022/day/4>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser::parse_usize,
    },
    winnow::{ModalResult, Parser, combinator::seq},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, usize, usize, usize)>,
}

fn parse_line(s: &mut &str) -> ModalResult<(usize, usize, usize, usize)> {
    seq!(parse_usize, _: "-", parse_usize, _: ",", parse_usize, _: "-", parse_usize).parse_next(s)
}

#[aoc(2022, 4)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        for mut l in input.lines() {
            self.line.push(parse_line(&mut l)?);
        }
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .filter(|(a, b, x, y)| (a <= x && y <= b) || (x <= a && b <= y))
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .filter(|(a, b, x, y)| (x <= b) && (a <= y))
            .count()
    }
}
