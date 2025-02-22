//! <https://adventofcode.com/2016/day/12>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Val {
    Reg(u8),
    Lit(isize),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Code {
    Cpy(Val, Val),
    Inc(Val),
    Dec(Val),
    Jnz(Val, Val),
    Tgl(Val),
}

#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
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
        let mut pc = Some(0usize);
        while let Some(i) = pc {
            pc = self.execute(i);
        }
    }
}

mod parser {
    use {
        super::*,
        crate::parser::parse_isize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, separated, seq},
            token::one_of,
        },
    };

    fn parse_val(s: &mut &str) -> ModalResult<Val> {
        alt((
            one_of(|c: char| c.is_ascii_lowercase()).map(|c| Val::Reg(c as u8 - b'a')),
            parse_isize.map(Val::Lit),
        ))
        .parse_next(s)
    }

    fn parse_line(s: &mut &str) -> ModalResult<Code> {
        alt((
            seq!(_: "cpy ", parse_val, _: " ", parse_val).map(|(a, b)| Code::Cpy(a, b)),
            seq!(_: "inc ", parse_val).map(|(a,)| Code::Inc(a)),
            seq!(_: "dec ", parse_val).map(|(a,)| Code::Dec(a)),
            seq!(_: "jnz ", parse_val, _: " ", parse_val).map(|(a, b)| Code::Jnz(a, b)),
            seq!(_: "tgl ", parse_val).map(|(a,)| Code::Tgl(a)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Code>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2016, 12)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.run();
        self.register[0] as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        self.register[2] = 1;
        self.run();
        self.register[0] as usize
    }
}
