//! <https://adventofcode.com/2015/day/2>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    line: Vec<(usize, usize, usize)>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<(usize, usize, usize)> {
        seq!(parse_usize, _: "x", parse_usize, _: "x", parse_usize).parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<(usize, usize, usize)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2015, 2)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut total = 0;
        for (l, w, h) in self.line.iter() {
            total += 2 * (l * w) + 2 * (w * h) + 2 * (h * l) + (l * w).min(w * h).min(h * l);
        }
        total
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut total = 0;
        for (l, w, h) in self.line.iter() {
            let mut v = [l, w, h];
            v.sort_unstable();
            total += 2 * (v[0] + v[1]) + l * w * h;
        }
        total
    }
}
