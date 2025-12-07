//! <https://adventofcode.com/2022/day/9>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser,
    },
    std::collections::HashMap,
    winnow::{
        ModalResult, Parser,
        ascii::newline,
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<()>,
}

fn parse(s: &mut &str) -> ModalResult<()> {
    ().parse_next(s)
}

#[aoc(2022, 9)]
impl AdventOfCode for Puzzle {
    // fn parse(&mut self, input: String) -> Result<String, ParseError> {
    //     // self.line = parse(&mut input.as_str())?;
    //     Ok(())
    // }
    fn part1(&mut self) -> Self::Output1 {
        1
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
