//! <https://adventofcode.com/2016/day/23>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Val {
    Reg(u8),
    Lit(isize),
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Code {
    Cpy(Val, Val),
    Inc(Val),
    Dec(Val),
    Jnz(Val, Val),
    Tgl(Val),
}

#[derive(Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Code>,
    register: [isize; 8],
    pc: Option<usize>,
}

impl Puzzle {
    fn get(&self, val: &Val) -> isize {
        match *val {
            Val::Reg(r) => self.register[r as usize],
            Val::Lit(l) => l,
        }
    }
    fn execute(&mut self, pc: usize) -> Option<usize> {
        if let Some(code) = self.line.get(pc) {
            match code {
                Code::Cpy(from, Val::Reg(reg)) => {
                    self.register[*reg as usize] = self.get(from);
                }
                Code::Inc(Val::Reg(reg)) => {
                    self.register[*reg as usize] += 1;
                }
                Code::Dec(Val::Reg(reg)) => {
                    self.register[*reg as usize] -= 1;
                }
                Code::Jnz(cond, offset) => {
                    if 0 != self.get(cond) {
                        return Some((pc as isize + self.get(offset)) as usize);
                    }
                }
                Code::Tgl(offset) => {
                    let off = self.get(offset);
                    if let Some(target) = self.line.get_mut((pc as isize + off) as usize) {
                        let new_code = match target {
                            Code::Cpy(op1, op2) => Code::Jnz(op1.clone(), op2.clone()),
                            Code::Inc(val) => Code::Dec(val.clone()),
                            Code::Dec(val) => Code::Inc(val.clone()),
                            Code::Jnz(op1, op2) => Code::Cpy(op1.clone(), op2.clone()),
                            Code::Tgl(val) => Code::Inc(val.clone()),
                        };
                        *target = new_code;
                    }
                }
                _ => {
                    dbg!(code);
                    // unreachable!()
                }
            }
            Some(pc + 1)
        } else {
            None
        }
    }
    fn run(&mut self) {
        self.register[0] = 7;
        let mut pc = Some(0usize);
        while let Some(i) = pc {
            pc = self.execute(i);
        }
    }
}

#[aoc_at(2016, 23)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parse_val = |s: &str| {
            let c: char = s.chars().next().unwrap();
            if c.is_ascii_alphabetic() {
                Val::Reg(c as u8 - b'a')
            } else {
                Val::Lit(s.parse::<isize>().unwrap())
            }
        };
        if let Ok(code) = regex!(r"^cpy ([a-z]|-?\d+) ([a-z]|-?\d+)$")
            .captures(block)
            .ok_or(ParseError)
        {
            self.line
                .push(Code::Cpy(parse_val(&code[1]), parse_val(&code[2])));
        } else if let Ok(code) = regex!(r"^inc ([a-z]|-?\d+)$")
            .captures(block)
            .ok_or(ParseError)
        {
            self.line.push(Code::Inc(parse_val(&code[1])));
        } else if let Ok(code) = regex!(r"^dec ([a-z]|-?\d+)$")
            .captures(block)
            .ok_or(ParseError)
        {
            self.line.push(Code::Dec(parse_val(&code[1])));
        } else if let Ok(code) = regex!(r"^jnz ([a-z]|-?\d+) ([a-z]|-?\d+)$")
            .captures(block)
            .ok_or(ParseError)
        {
            self.line
                .push(Code::Jnz(parse_val(&code[1]), parse_val(&code[2])));
        } else if let Ok(code) = regex!(r"^tgl ([a-z]|-?\d+)$")
            .captures(block)
            .ok_or(ParseError)
        {
            self.line.push(Code::Tgl(parse_val(&code[1])));
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.run();
        self.register[0]
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
