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
    line: String,
}

fn parse_pair(str: &str) -> IResult<&str, (u64, u64)> {
    delimited(tag("mul("), pair(terminated(u64, tag(",")), u64), tag(")"))(str)
}

fn parse_pair1(str: &str) -> IResult<&str, (u64, u64)> {
    alt((parse_pair, preceded(anychar, parse_pair1)))(str)
}

fn parse1(str: &str) -> IResult<&str, Vec<(u64, u64)>> {
    many1(parse_pair1)(str)
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
enum Inst {
    #[default]
    Do,
    Dont,
    Mul(u64, u64),
}

fn parse2_inst0(str: &str) -> IResult<&str, Inst> {
    let (remain, _) = tag("do()")(str)?;
    Ok((remain, Inst::Do))
}

fn parse2_inst1(str: &str) -> IResult<&str, Inst> {
    let (remain, _) = tag("don't()")(str)?;
    Ok((remain, Inst::Dont))
}

fn parse2_inst2(str: &str) -> IResult<&str, Inst> {
    let (remain, mul) =
        delimited(tag("mul("), pair(terminated(u64, tag(",")), u64), tag(")"))(str)?;
    Ok((remain, Inst::Mul(mul.0, mul.1)))
}

fn parse2_inst(str: &str) -> IResult<&str, Inst> {
    alt((parse2_inst0, parse2_inst1, parse2_inst2))(str)
}

fn parse2_aux(str: &str) -> IResult<&str, Inst> {
    alt((parse2_inst, preceded(anychar, parse2_aux)))(str)
}

fn parse2(str: &str) -> IResult<&str, Vec<Inst>> {
    many1(parse2_aux)(str)
}

#[aoc(2024, 3)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = input;
        Ok("".to_string())
    }
    fn part1(&mut self) -> Self::Output1 {
        let line = parse1(self.line.as_str()).expect("parse error").1;
        line.iter().map(|(a, b)| (a * b) as usize).sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let line = parse2(self.line.as_str()).expect("parse error").1;
        line.iter()
            .fold((true, 0_usize), |acum, inst| match (acum.0, inst) {
                (_, Inst::Do) => (true, acum.1),
                (_, Inst::Dont) => (false, acum.1),
                (false, _) => (false, acum.1),
                (true, Inst::Mul(a, b)) => (true, acum.1 + (a * b) as usize),
            })
            .1
    }
}
