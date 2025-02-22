//! <https://adventofcode.com/2017/day/13>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
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

    fn parse_line(s: &mut &str) -> ModalResult<(usize, usize)> {
        seq!(parse_usize, _: ": ", parse_usize).parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<(usize, usize)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2017, 13)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut severity: usize = 0;
        for (depth, range) in self.line.iter() {
            let cycle: usize = 2 * (*range - 1);
            if *depth % cycle == 0 {
                severity += depth * *range;
            }
        }
        severity
    }
    fn part2(&mut self) -> Self::Output2 {
        'next_challenge: for delay in 0.. {
            for (depth, range) in self.line.iter() {
                let cycle: usize = 2 * (*range - 1);
                if (*depth + delay) % cycle == 0 {
                    continue 'next_challenge;
                }
            }
            return delay;
        }
        0
    }
}
