//! <https://adventofcode.com/2017/day/23>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        color::REVERT,
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{HashMap, VecDeque},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Inst>,
}

#[aoc(2017, 23)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(Inst::try_from(block)?);
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut processor: Runtime = Runtime::initialize(-1, &self.line);
        loop {
            if let Some(c) = processor.execute() {
                return c;
            }
        }
    }
    fn part2(&mut self) -> Self::Output2 {
        println!();
        let mut b = 67 * 100 + 100000;
        let c = b + 17000;
        // let mut d = 2;
        let e = 2;
        let f = 1;
        let mut h = 0;
        loop {
            // println!("{REVERT}B:{b:>8}, D:{d:>8}, E:{e:>8}, F:{f:>8}, H:{h:>8}");
            // //            if d * e == b {
            // //                f = 0;
            // //            }
            // e += 1;
            // if e != b {
            //     continue;
            // }
            // e = b;

            // //            d += 1;
            // //            if d != b {
            // //                // e = 2;
            // //                continue;
            // //            }
            // // d = b;

            // //            if f == 0 {
            // //                h += 1;
            // //            }
            if (2..=((b as f64).sqrt() as usize)).any(|k| b % k == 0) {
                h += 1;
            }

            if c == b {
                break;
            }
            b += 17;
            // d = 2;
            // e = 2;
        }
        h
    }
}

type Channel = [VecDeque<usize>; 2];
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum RuntimeState {
    #[default]
    None,
    Receiving(usize),
    Sending(usize, usize),
}

#[derive(Debug, Default, Eq, PartialEq)]
struct Runtime {
    id: usize,
    pc: usize,
    register: HashMap<Val, isize>,
    memory: HashMap<usize, Inst>,
    frequency: usize,
    state: RuntimeState,
    debug_counter: usize,
}

impl Runtime {
    fn initialize(iid: isize, code: &[Inst]) -> Runtime {
        let mut memory: HashMap<usize, Inst> = HashMap::new();
        for (addr, inst) in code.iter().enumerate() {
            memory.insert(addr, *inst);
        }
        let mut register: HashMap<Val, isize> = HashMap::new();
        if 0 <= iid {
            register.insert(Val::Reg('p'), iid);
        }
        Runtime {
            id: iid as usize,
            pc: 0,
            register,
            memory,
            frequency: 0,
            state: RuntimeState::None,
            debug_counter: 0,
        }
    }
    fn get(&self, val: &Val) -> isize {
        match val {
            Val::Lit(n) => *n,
            _ => *self.register.get(val).unwrap_or(&0),
        }
    }
    fn set(&mut self, reg: &Val, val: isize) {
        self.register.insert(*reg, val);
    }
    fn execute(&mut self) -> Option<usize> {
        if let Some(inst) = self.memory.get(&self.pc) {
            let ins = *inst;
            // println!("{:>3} {:?}", self.pc, ins);
            match ins {
                Inst::Set(op1, op2) => {
                    let y = self.get(&op2);
                    self.set(&op1, y);
                }
                Inst::Sub(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    self.set(&op1, x - y);
                }
                Inst::Mul(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    self.set(&op1, x * y);
                    self.debug_counter += 1;
                }
                Inst::Jnz(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    if 0 != x {
                        let n: isize = self.pc as isize + y - 1;
                        assert!(0 <= n);
                        self.pc = n as usize;
                    }
                }
            };
            self.pc += 1;
            None
        } else {
            Some(self.debug_counter)
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Val {
    Reg(char),
    Lit(isize),
}

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Inst {
    Set(Val, Val),
    Sub(Val, Val),
    Mul(Val, Val),
    Jnz(Val, Val),
}

impl TryFrom<&str> for Inst {
    type Error = ParseError;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        // dbg!(value);
        let arg2ll = regex!(r"^([[:lower:]]{3}) (-?[[:digit:]]+) (-?[[:digit:]]+)$");
        let arg2lr = regex!(r"^([[:lower:]]{3}) (-?[[:digit:]]+) ([[:lower:]])$");
        let arg2rl = regex!(r"^([[:lower:]]{3}) ([[:lower:]]) (-?[[:digit:]]+)$");
        let arg2rr = regex!(r"^([[:lower:]]{3}) ([[:lower:]]) ([[:lower:]])$");
        if let Some(segment) = arg2ll.captures(value) {
            let op1: Val = Val::Lit(segment[2].parse::<isize>()?);
            let op2: Val = Val::Lit(segment[3].parse::<isize>()?);
            let ins = match &segment[1] {
                "set" => Inst::Set(op1, op2),
                "sub" => Inst::Sub(op1, op2),
                "mul" => Inst::Mul(op1, op2),
                "jnz" => Inst::Jnz(op1, op2),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        if let Some(segment) = arg2lr.captures(value) {
            let op1: Val = Val::Lit(segment[2].parse::<isize>()?);
            let op2: Val = Val::Reg(segment[3].chars().next().ok_or(ParseError)?);
            let ins = match &segment[1] {
                "set" => Inst::Set(op1, op2),
                "sub" => Inst::Sub(op1, op2),
                "mul" => Inst::Mul(op1, op2),
                "jnz" => Inst::Jnz(op1, op2),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        if let Some(segment) = arg2rl.captures(value) {
            let op1: Val = Val::Reg(segment[2].chars().next().ok_or(ParseError)?);
            let op2: Val = Val::Lit(segment[3].parse::<isize>()?);
            let ins = match &segment[1] {
                "set" => Inst::Set(op1, op2),
                "sub" => Inst::Sub(op1, op2),
                "mul" => Inst::Mul(op1, op2),
                "jnz" => Inst::Jnz(op1, op2),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        if let Some(segment) = arg2rr.captures(value) {
            let op1: Val = Val::Reg(segment[2].chars().next().ok_or(ParseError)?);
            let op2: Val = Val::Reg(segment[3].chars().next().ok_or(ParseError)?);
            let ins = match &segment[1] {
                "set" => Inst::Set(op1, op2),
                "sub" => Inst::Sub(op1, op2),
                "mul" => Inst::Mul(op1, op2),
                "jnz" => Inst::Jnz(op1, op2),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        Err(ParseError)
    }
}
