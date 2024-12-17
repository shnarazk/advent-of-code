//! <https://adventofcode.com/2024/day/17>
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        parser::parse_usize,
    },
    itertools::Itertools,
    serde::Serialize,
    std::{cmp::Reverse, collections::BinaryHeap},
    winnow::{
        ascii::{dec_uint, newline},
        combinator::{separated, seq},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    reg: [usize; 3],
    code: Vec<u8>,
    ip: usize,
    output: Vec<u8>,
}

impl Puzzle {
    fn test_run(&self, i: usize) -> Vec<u8> {
        let mut pc = self.clone();
        pc.reg[0] = i;
        pc.run();
        pc.output
    }
    fn fetch(&mut self) -> Option<(u8, u8)> {
        if let Some(a) = self.code.get(self.ip).copied() {
            if let Some(b) = self.code.get(self.ip + 1).copied() {
                return Some((a, b));
            }
        }
        None
    }
    fn combo_opland(&self, d: u8) -> usize {
        match d {
            0..=3 => d as usize,
            4 => self.reg[0],
            5 => self.reg[1],
            6 => self.reg[2],
            _ => unreachable!(),
        }
    }
    fn inc_ip(&mut self) {
        self.ip += 2;
    }
    fn execute(&mut self, opc: u8, lit_opl: u8) {
        match opc {
            0 => {
                // adv
                let numer = self.reg[0];
                let denom = 2_usize.pow(self.combo_opland(lit_opl) as u32);
                self.reg[0] = numer / denom;
                self.inc_ip();
            }
            1 => {
                self.reg[1] ^= lit_opl as usize; // bxl
                self.inc_ip();
            }
            2 => {
                self.reg[1] = self.combo_opland(lit_opl) % 8; // bst
                self.inc_ip();
            }
            3 => {
                if self.reg[0] != 0 {
                    self.ip = lit_opl as usize;
                } else {
                    self.inc_ip();
                }
            }
            4 => {
                self.reg[1] ^= self.reg[2];
                self.inc_ip();
            }
            5 => {
                let val = self.combo_opland(lit_opl) % 8;
                self.output.push(val as u8);
                self.inc_ip();
            }
            6 => {
                // bdv
                let numer = self.reg[0];
                let denom = 2_usize.pow(self.combo_opland(lit_opl) as u32);
                self.reg[1] = numer / denom;
                self.inc_ip();
            }
            7 => {
                // cdv
                let numer = self.reg[0];
                let denom = 2_usize.pow(self.combo_opland(lit_opl) as u32);
                self.reg[2] = numer / denom;
                self.inc_ip();
            }
            _ => (),
        }
    }
    fn run(&mut self) -> &[u8] {
        self.ip = 0;
        while let Some((c, l)) = self.fetch() {
            self.execute(c, l);
        }
        &self.output
    }
}

fn parse_reg(s: &mut &str) -> PResult<usize> {
    seq!( _: "Register ", one_of(&['A', 'B', 'C']), _: ": ", parse_usize)
        .map(|(_, val)| val)
        .parse_next(s)
}
fn parse_program(s: &mut &str) -> PResult<Vec<u8>> {
    ("Program: ", separated(1.., dec_uint::<_, u8, _>, ","))
        .map(|(_, v)| v)
        .parse_next(s)
}

fn parse(s: &mut &str) -> PResult<(usize, usize, usize, Vec<u8>)> {
    seq!(
        parse_reg, _: newline,
        parse_reg, _: newline,
        parse_reg, _: newline,
        _: newline,
        parse_program)
    .parse_next(s)
}

#[aoc_at(2024, 17)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = usize;
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let (r1, r2, r3, code) = parse(&mut input.as_str())?;
        self.reg = [r1, r2, r3];
        self.code = code;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.run();
        self.output.iter().map(|n| format!("{n}")).join(",")
    }
    fn part2(&mut self) -> Self::Output2 {
        // 2,4(A): B(3bit) <- A % 8
        // 1,5   : B(3bit) <- B ^ b101
        // 7,5(B): C <- A / 2**B
        // 0,3   : A <- A / 8
        // 4.1   : B <- B ^ C
        // 1,6   : B <- B ^ 6
        // 5,5(B): output <- B % 8
        // 3,0   : if A != 0 { goto 0 }
        let cond = self.code.iter().rev().cloned().collect::<Vec<_>>();
        fn compatible(base: &[u8], cand: &[u8]) -> bool {
            let len = cand.len();
            cand.iter()
                .enumerate()
                .all(|(i, n)| *n == base[len - i - 1])
        }
        let mut to_visit: BinaryHeap<Reverse<(usize, usize)>> = BinaryHeap::new();
        to_visit.push(Reverse((0, 0)));
        while let Some(Reverse((done, ans))) = to_visit.pop() {
            if done == cond.len() {
                return ans;
            }
            for i in 0..7 {
                let a = ans * 8 + i;
                if compatible(&cond, self.test_run(a).as_ref()) {
                    to_visit.push(Reverse((done + 1, a)));
                }
            }
        }
        unreachable!()
    }
}
