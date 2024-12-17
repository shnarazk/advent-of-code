//! <https://adventofcode.com/2024/day/17>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::neighbors,
        parser::{parse_isize, parse_usize},
    },
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{collections::HashMap, hash::BuildHasherDefault},
    winnow::{
        ascii::{dec_uint, newline},
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    reg: [isize; 3],
    code: Vec<u8>,
    ip: usize,
    output: String,
}

impl Puzzle {
    fn fetch(&mut self) -> Option<(u8, u8)> {
        if let Some(a) = self.code.get(self.ip).map(|p| *p) {
            if let Some(b) = self.code.get(self.ip + 1).map(|p| *p) {
                return Some((a, b));
            }
        }
        None
    }
    fn combo_opland(&self, d: u8) -> isize {
        match d {
            0 | 1 | 2 | 3 => d as isize,
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
                let denom = 2_isize.pow(self.combo_opland(lit_opl) as u32);
                self.reg[0] = numer / denom;
                self.inc_ip();
            }
            1 => {
                self.reg[1] ^= lit_opl as isize; // bxl
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
                if !self.output.is_empty() {
                    self.output.push(',');
                }
                self.output.push_str(format!("{val}").as_str());
                self.inc_ip();
            }
            6 => {
                // bdv
                let numer = self.reg[0];
                let denom = 2_isize.pow(self.combo_opland(lit_opl) as u32);
                self.reg[1] = numer / denom;
                self.inc_ip();
            }
            7 => {
                // cdv
                let numer = self.reg[0];
                let denom = 2_isize.pow(self.combo_opland(lit_opl) as u32);
                self.reg[2] = numer / denom;
                self.inc_ip();
            }
            _ => (),
        }
    }
    fn run(&mut self) {
        self.ip = 0;
        while let Some((c, l)) = self.fetch() {
            self.execute(c, l);
        }
        println!("{}", self.output);
    }
}

fn parse_reg(s: &mut &str) -> PResult<isize> {
    seq!( _: "Register ", one_of(&['A', 'B', 'C']), _: ": ", parse_isize)
        .map(|(_, val)| val)
        .parse_next(s)
}
fn parse_program(s: &mut &str) -> PResult<Vec<u8>> {
    ("Program: ", separated(1.., dec_uint::<_, u8, _>, ","))
        .map(|(_, v)| v)
        .parse_next(s)
}

fn parse(s: &mut &str) -> PResult<(isize, isize, isize, Vec<u8>)> {
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
    fn end_of_data(&mut self) {
        // dbg!(&self.reg);
        // self.reg[2] = 9;
        // let mut pc = Puzzle {
        //     code: vec![4, 0],
        //     reg: [2024, 2024, 43690],
        //     ..Default::default()
        // };
        // pc.run();
        // dbg!(&pc.reg);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.run();
        dbg!(&self.reg);
        self.output.clone()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
