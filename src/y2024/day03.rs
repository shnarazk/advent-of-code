//! <https://adventofcode.com/2024/day/3>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    nom::{
        branch::alt,
        bytes::complete::tag,
        character::complete::{anychar, u64},
        multi::many1,
        sequence::{delimited, pair, preceded, terminated},
        IResult,
    },
    serde::Serialize,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<Inst>,
}

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
enum Inst {
    Do,
    Dont,
    Mul(u64, u64),
}

fn parse_inst0(str: &str) -> IResult<&str, Inst> {
    let (remain, _) = tag("do()")(str)?;
    Ok((remain, Inst::Do))
}

fn parse_inst1(str: &str) -> IResult<&str, Inst> {
    let (remain, _) = tag("don't()")(str)?;
    Ok((remain, Inst::Dont))
}

fn parse_inst2(str: &str) -> IResult<&str, Inst> {
    let (remain, mul) =
        delimited(tag("mul("), pair(terminated(u64, tag(",")), u64), tag(")"))(str)?;
    Ok((remain, Inst::Mul(mul.0, mul.1)))
}

fn parse_inst(str: &str) -> IResult<&str, Inst> {
    alt((parse_inst0, parse_inst1, parse_inst2))(str)
}

fn parse_aux(str: &str) -> IResult<&str, Inst> {
    alt((parse_inst, preceded(anychar, parse_aux)))(str)
}

fn parse(str: &str) -> IResult<&str, Vec<Inst>> {
    many1(parse_aux)(str)
}

#[aoc(2024, 3)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(input.as_str())?.1;
        Ok("".to_string())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().fold(0_usize, |accum, inst| match inst {
            Inst::Mul(a, b) => accum + (a * b) as usize,
            _ => accum,
        })
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .fold((true, 0_usize), |accum, inst| match (accum.0, inst) {
                (_, Inst::Do) => (true, accum.1),
                (_, Inst::Dont) => (false, accum.1),
                (false, _) => (false, accum.1),
                (true, Inst::Mul(a, b)) => (true, accum.1 + (a * b) as usize),
            })
            .1
    }
}
