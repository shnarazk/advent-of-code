//! <https://adventofcode.com/2020/day/8>
use crate::framework::{AdventOfCode, ParseError, aoc_at};

#[derive(Clone, Debug, PartialEq)]
enum Instruction {
    Acc(isize),
    Jmp(isize),
    Nop(isize),
}

impl Instruction {
    fn flip(&self) -> Option<Instruction> {
        match self {
            Instruction::Acc(_) => None,
            Instruction::Jmp(n) => Some(Instruction::Nop(*n)),
            Instruction::Nop(n) => Some(Instruction::Jmp(*n)),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    code: Vec<(Instruction, bool)>,
}

mod parser {
    use {
        super::Instruction,
        crate::parser::parse_isize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, opt, separated},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<(Instruction, bool)> {
        alt((
            ("acc ", opt('+'), parse_isize).map(|(_, _, n)| Instruction::Acc(n)),
            ("jmp ", opt('+'), parse_isize).map(|(_, _, n)| Instruction::Jmp(n)),
            ("nop ", opt('+'), parse_isize).map(|(_, _, n)| Instruction::Nop(n)),
        ))
        .map(|i| (i, false))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<(Instruction, bool)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc_at(2020, 8)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.code = parser::parse(&mut input)?;
        Self::parsed()
    }
    fn part1(&mut self) -> isize {
        if let Some(result) = CPU::run1(&mut self.code) {
            return result.accumulator;
        }
        0
    }
    fn part2(&mut self) -> isize {
        for i in 0..self.code.len() {
            if let Some(mut variant) = flip(&self.code, i) {
                if let Some(result) = CPU::run2(&mut variant) {
                    return result.accumulator;
                }
            }
        }
        0
    }
}

const ABORT: usize = 10_000_000_000_000;

#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, PartialEq)]
struct CPU {
    accumulator: isize,
    ip: usize,
}

impl CPU {
    fn default() -> Self {
        CPU {
            accumulator: 0,
            ip: 0,
        }
    }
    fn run1(codes: &mut [(Instruction, bool)]) -> Option<CPU> {
        let mut cpu = CPU::default();
        loop {
            if cpu.stopped(codes) {
                return Some(cpu);
            }
            if cpu.should_be_stopped(codes) {
                return Some(cpu);
            }
            cpu.execute(codes);
            if cpu.ip == ABORT {
                return None;
            }
        }
    }
    fn run2(codes: &mut [(Instruction, bool)]) -> Option<CPU> {
        let mut cpu = CPU::default();
        loop {
            if cpu.stopped(codes) {
                return Some(cpu);
            }
            if cpu.should_be_stopped(codes) {
                return None;
            }
            cpu.execute(codes);
            if cpu.ip == ABORT {
                return None;
            }
        }
    }
    fn decode(&mut self, inst: &Instruction) {
        match inst {
            Instruction::Acc(n) => {
                self.accumulator += n;
            }
            Instruction::Jmp(n) => {
                let new_ip = self.ip as isize + n - 1;
                if new_ip < 0 {
                    self.ip = ABORT;
                } else {
                    self.ip = new_ip as usize;
                }
            }
            Instruction::Nop(_) => (),
        }
    }
    fn execute(&mut self, codes: &[(Instruction, bool)]) {
        let code = &codes[self.ip].0;
        self.decode(code);
        if self.ip < ABORT {
            self.ip += 1;
        }
    }
    fn stopped(&mut self, codes: &mut [(Instruction, bool)]) -> bool {
        codes.len() == self.ip
    }
    fn should_be_stopped(&mut self, codes: &mut [(Instruction, bool)]) -> bool {
        let first = codes[self.ip].1;
        codes[self.ip].1 = true;
        first
    }
}

fn flip(codes: &[(Instruction, bool)], at: usize) -> Option<Vec<(Instruction, bool)>> {
    let mut newcodes: Vec<(Instruction, bool)> = Vec::new();
    for (n, inst) in codes.iter().enumerate() {
        if n == at {
            if let Some(flipped) = inst.0.flip() {
                newcodes.push((flipped, false));
            } else {
                return None;
            }
        } else {
            newcodes.push((inst.0.clone(), false));
        }
    }
    Some(newcodes)
}
