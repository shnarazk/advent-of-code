//! <https://adventofcode.com/2017/day/18>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Val {
    Reg(char),
    Lit(isize),
}

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Inst {
    Snd(Val),
    Set(Val, Val),
    Add(Val, Val),
    Mul(Val, Val),
    Mod(Val, Val),
    Rcv(Val),
    Jgz(Val, Val),
}

impl TryFrom<&str> for Inst {
    type Error = ParseError;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        dbg!(value);
        let arg1l = regex!(r"^([[:lower:]]{3}) (-?[[:digit:]]+)$");
        let arg1r = regex!(r"^([[:lower:]]{3}) ([[:lower:]])$");
        let arg2ll = regex!(r"^([[:lower:]]{3}) (-?[[:digit:]]+) (-?[[:digit:]]+)$");
        let arg2lr = regex!(r"^([[:lower:]]{3}) (-?[[:digit:]]+) ([[:lower:]])$");
        let arg2rl = regex!(r"^([[:lower:]]{3}) ([[:lower:]]) (-?[[:digit:]]+)$");
        let arg2rr = regex!(r"^([[:lower:]]{3}) ([[:lower:]]) ([[:lower:]])$");
        if let Some(segment) = arg1l.captures(value) {
            let val: Val = Val::Lit(segment[2].parse::<isize>()?);
            let ins = match &segment[1] {
                "snd" => Inst::Snd(val),
                "rcv" => Inst::Rcv(val),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        if let Some(segment) = arg1r.captures(value) {
            let reg: Val = Val::Reg(segment[2].chars().next().ok_or(ParseError)?);
            let ins = match &segment[1] {
                "snd" => Inst::Snd(reg),
                "rcv" => Inst::Rcv(reg),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        if let Some(segment) = arg2ll.captures(value) {
            let op1: Val = Val::Lit(segment[2].parse::<isize>()?);
            let op2: Val = Val::Lit(segment[3].parse::<isize>()?);
            let ins = match &segment[1] {
                "set" => Inst::Set(op1, op2),
                "add" => Inst::Add(op1, op2),
                "mul" => Inst::Mul(op1, op2),
                "mod" => Inst::Mod(op1, op2),
                "jgz" => Inst::Jgz(op1, op2),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        if let Some(segment) = arg2lr.captures(value) {
            let op1: Val = Val::Lit(segment[2].parse::<isize>()?);
            let op2: Val = Val::Reg(segment[2].chars().next().ok_or(ParseError)?);
            let ins = match &segment[1] {
                "set" => Inst::Set(op1, op2),
                "add" => Inst::Add(op1, op2),
                "mul" => Inst::Mul(op1, op2),
                "mod" => Inst::Mod(op1, op2),
                "jgz" => Inst::Jgz(op1, op2),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        if let Some(segment) = arg2rl.captures(value) {
            let op1: Val = Val::Reg(segment[2].chars().next().ok_or(ParseError)?);
            let op2: Val = Val::Lit(segment[3].parse::<isize>()?);
            let ins = match &segment[1] {
                "set" => Inst::Set(op1, op2),
                "add" => Inst::Add(op1, op2),
                "mul" => Inst::Mul(op1, op2),
                "mod" => Inst::Mod(op1, op2),
                "jgz" => Inst::Jgz(op1, op2),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        if let Some(segment) = arg2rr.captures(value) {
            let op1: Val = Val::Reg(segment[2].chars().next().ok_or(ParseError)?);
            let op2: Val = Val::Reg(segment[2].chars().next().ok_or(ParseError)?);
            let ins = match &segment[1] {
                "set" => Inst::Set(op1, op2),
                "add" => Inst::Add(op1, op2),
                "mul" => Inst::Mul(op1, op2),
                "mod" => Inst::Mod(op1, op2),
                "jgz" => Inst::Jgz(op1, op2),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        Err(ParseError)
    }
}
#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Inst>,
}

#[aoc(2017, 18)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(Inst::try_from(block)?);
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
