//! <https://adventofcode.com/2021/day/>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<()>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ascii::{alpha1, newline, space1},
            combinator::{alt, separated, seq},
            PResult, Parser,
        },
    };

    fn parse_line(s: &mut &str) -> PResult<()> {
        ().parse_next(s)
    }

    pub fn parse(s: &mut &str) -> PResult<Vec<()>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2021, 0)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parser::parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
