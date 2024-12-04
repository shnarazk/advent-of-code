//! <https://adventofcode.com/2024/day/4>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
    },
    nom::{
        bytes::complete::{tag, take},
        character::complete::{alpha1, alphanumeric1, anychar, digit1, newline, u64},
        multi::{many1, many_till, separated_list1},
        sequence::{separated_pair, terminated, tuple},
        IResult,
    },
    serde::Serialize,
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
}

fn parse(str: &str) -> IResult<&str, Vec<Vec<char>>> {
    let (r, v) = separated_list1(newline, alpha1)(str)?;
    Ok((
        r,
        v.iter()
            .map(|v| v.chars().collect::<Vec<char>>())
            .collect::<Vec<_>>(),
    ))
}

#[aoc(2024, 4)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(input.as_str())?.1;
        Ok("".to_string())
    }
    fn end_of_data(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        1
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
