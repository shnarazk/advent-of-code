//! <https://adventofcode.com/2024/day/3>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
    },
    nom::{
        branch::alt,
        bytes::complete::{tag, take},
        character::complete::{alpha1, alphanumeric1, anychar, digit1, newline, u64},
        multi::{many0, many1, many_till, separated_list1},
        sequence::{delimited, pair, preceded, separated_pair, terminated, tuple},
        IResult,
    },
    serde::Serialize,
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<(u64, u64)>,
}

fn parse_pair(str: &str) -> IResult<&str, (u64, u64)> {
    delimited(tag("mul("), pair(terminated(u64, tag(",")), u64), tag(")"))(str)
}

fn parse_pair1(str: &str) -> IResult<&str, (u64, u64)> {
    alt((parse_pair, preceded(anychar, parse_pair1)))(str)
}

fn parse(str: &str) -> IResult<&str, Vec<(u64, u64)>> {
    many1(parse_pair1)(str)
}

#[aoc(2024, 3)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(input.as_str())?.1;
        Ok("".to_string())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().map(|(a, b)| (a * b) as usize).sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
