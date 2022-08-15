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

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Val {
    Reg(char),
    Lit(isize),
}

impl Val {
    fn is_lit(&self) -> bool {
        matches!(self, Val::Lit(_))
    }
    fn is_reg(&self) -> bool {
        !self.is_lit()
    }
}

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
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

#[derive(Debug, Default, Eq, PartialEq)]
struct Runtime {
    pc: usize,
    register: HashMap<Val, isize>,
    memory: HashMap<usize, Inst>,
    output: Vec<usize>,
}

impl Runtime {
    fn initialize(code: &[Inst]) -> Runtime {
        let mut memory: HashMap<usize, Inst> = HashMap::new();
        for (addr, inst) in code.iter().enumerate() {
            memory.insert(addr, *inst);
        }
        Runtime {
            pc: 0,
            register: HashMap::new(),
            memory,
            output: Vec::new(),
        }
    }
    fn get(&self, val: &Val) -> isize {
        match val {
            Val::Lit(n) => *n,
            _ => *self.register.get(&val).unwrap_or(&0),
        }
    }
    fn set(&mut self, reg: &Val, val: isize) {
        self.register.insert(*reg, val);
    }
    fn execute(&mut self) {
        match self
            .memory
            .get(&self.pc)
            .expect("PC points an invalid address")
        {
            Inst::Snd(op1) => {
                let x = self.get(op1);
            }
            Inst::Set(op1, op2) if op1.is_reg() => {
                let y = self.get(op2);
                self.set(op1, y);
            }
            Inst::Add(op1, op2) => {
                let x = self.get(op1);
                let y = self.get(op2);
                self.set(op1, x + y);
            }
            Inst::Mul(op1, op2) => {
                let x = self.get(op1);
                let y = self.get(op2);
                self.set(op1, x * y);
            }
            Inst::Mod(op1, op2) => {
                let x = self.get(op1);
                let y = self.get(op2);
                self.set(op1, x % y);
            }
            Inst::Rcv(op1) => {
                let x = self.get(op1);
                if x != 0 {}
            }
            Inst::Jgz(op1, op2) => {
                let x = self.get(op1);
                let y = self.get(op2);
                if 0 < x {
                    self.pc = self.pc.checked_add(y).expect("pc has an invalid value");
                }
            }
            _ => unreachable!(),
        }
        self.pc += 1;
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
