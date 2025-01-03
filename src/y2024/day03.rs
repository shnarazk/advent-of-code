//! <https://adventofcode.com/2024/day/3>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser::parse_usize,
    },
    serde::Serialize,
    winnow::{
        combinator::{alt, preceded, repeat, seq},
        token::any,
        PResult, Parser,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<Inst>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
enum Inst {
    Do,
    Dont,
    Mul(usize, usize),
}

fn parse_inst0(str: &mut &str) -> PResult<Inst> {
    "do()".map(|_| Inst::Do).parse_next(str)
}

fn parse_inst1(str: &mut &str) -> PResult<Inst> {
    "don't()".map(|_| Inst::Dont).parse_next(str)
}

fn parse_inst2(str: &mut &str) -> PResult<Inst> {
    seq!(
        _: "mul(", parse_usize, _: ",", parse_usize, _: ")")
    .map(|(m1, m2)| Inst::Mul(m1, m2))
    .parse_next(str)
}

fn parse_inst(str: &mut &str) -> PResult<Inst> {
    alt((parse_inst0, parse_inst1, parse_inst2)).parse_next(str)
}

fn parse_aux(str: &mut &str) -> PResult<Inst> {
    alt((parse_inst, preceded(any, parse_aux))).parse_next(str)
}

fn parse(str: &mut &str) -> PResult<Vec<Inst>> {
    repeat(0.., parse_aux).parse_next(str)
}

#[aoc(2024, 3)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().fold(0_usize, |accum, inst| match inst {
            Inst::Mul(a, b) => accum + a * b,
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
                (true, Inst::Mul(a, b)) => (true, accum.1 + a * b),
            })
            .1
    }
}
