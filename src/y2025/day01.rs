//! <https://adventofcode.com/2025/day/1>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<isize>,
}

mod parser {
    use {
        crate::parser::parse_isize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<isize> {
        seq!(alt(("L", "R")), parse_isize)
            .parse_next(s)
            .map(|(s, n)| n * if s == "L" { -1 } else { 1 })
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<isize>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2025, 1)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut pos: isize = 50;
        let mut zeros: usize = 0;
        for a in self.line.iter() {
            pos = (pos + a) % 100;
            zeros += (pos == 0) as usize;
        }
        zeros
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut pos: isize = 50;
        let mut zeros: usize = 0;
        for a in self.line.iter() {
            let old = pos;
            pos += a;
            zeros += (old > 0 && pos <= 0) as usize;
            zeros += pos.unsigned_abs() / 100;
            pos = pos.rem_euclid(100);
        }
        zeros
    }
}
