//! <https://adventofcode.com/2016/day/03>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ascii::{newline, space0, space1},
            combinator::{separated, seq},
            ModalResult, Parser,
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Vec<usize>> {
        seq!(_: space0, separated(3, parse_usize, space1))
            .map(|(v,)| v)
            .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Vec<usize>>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2016, 3)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .filter(|vec| {
                let mut v: Vec<usize> = vec.to_vec();
                v.sort_unstable();
                v[2] < v[0] + v[1]
            })
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut count = 0;
        for j in 0..self.line.len() / 3 {
            for i in 0..3 {
                let mut v = [
                    self.line[j * 3][i],
                    self.line[j * 3 + 1][i],
                    self.line[j * 3 + 2][i],
                ];
                v.sort_unstable();
                if v[2] < v[0] + v[1] {
                    count += 1;
                }
            }
        }
        count
    }
}
