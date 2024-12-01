//! <https://adventofcode.com/2024/day/1>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    nom::{
        bytes::complete::{tag, take},
        character::complete::{alpha1, alphanumeric1, anychar, digit1, newline, space1, u64},
        multi::{many1, many_till, separated_list1},
        sequence::{pair, separated_pair, terminated, tuple},
        IResult,
    },
    serde::Serialize,
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<(u64, u64)>,
}

fn parse(str: &str) -> IResult<&str, Vec<(u64, u64)>> {
    let (remain1, v) = many1(pair(terminated(u64, space1), terminated(u64, newline)))(str)?;
    Ok((remain1, v))
}

#[aoc(2024, 1)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let str = input.as_str();
        let Ok((_remain1, v)) = parse(str) else {
            return Err(ParseError);
        };
        self.line = v;
        Ok("".to_string())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut l = self.line.iter().map(|p| p.0).collect::<Vec<u64>>();
        let mut r = self.line.iter().map(|p| p.1).collect::<Vec<u64>>();
        l.sort();
        r.sort();
        dbg!(l
            .iter()
            .zip(r.iter())
            .collect::<Vec<_>>()
            .iter()
            .map(|(a, b)| a.abs_diff(**b) as usize)
            .sum::<usize>())
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
