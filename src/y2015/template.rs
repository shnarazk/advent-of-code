//! <https://adventofcode.com/2015/day/>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::neighbors,
    },
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<()>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline, space1},
            combinator::{alt, separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<()> {
        ().parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<()>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2015, 0)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
