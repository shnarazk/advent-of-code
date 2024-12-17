//! <https://adventofcode.com/2024/day/17>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::neighbors,
        parser::{parse_isize, parse_usize},
        progress,
    },
    itertools::Itertools,
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap},
        hash::BuildHasherDefault,
    },
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
    input: String,
    output: Vec<u8>,
    break_flag: bool,
}

fn to_num(vec: &[u8]) -> isize {
    let mut result: isize = 0;
    for d in vec.iter() {
        result *= 8;
        result += *d as isize;
    }
    result
}

impl Puzzle {
    fn reset(&self, i: isize) -> Puzzle {
        let mut pc = self.clone();
        pc.reg[0] = i;
        pc
    }
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
                self.output.push(val as u8);
                if self.break_flag && self.output != self.code[0..self.output.len()] {
                    self.ip = self.code.len();
                }
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
    fn run(&mut self) -> &[u8] {
        self.ip = 0;
        while let Some((c, l)) = self.fetch() {
            self.execute(c, l);
        }
        &self.output
    }
    fn run_breakable(&mut self) {
        self.break_flag = true;
        self.ip = 0;
        while let Some((c, l)) = self.fetch() {
            self.execute(c, l);
        }
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
        self.input = self.code.iter().map(|n| format!("{n}")).join(",");
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
        //
        let mut cond = self.code.clone();
        cond.reverse();
        dbg!(&cond);
        let mut result: Vec<u8> = Vec::new();
        fn compatible(base: &[u8], cand: &[u8]) -> bool {
            let len = cand.len();
            cand.iter()
                .enumerate()
                .all(|(i, n)| *n == base[len - i - 1])
        }
        type SEARCH = (usize, Vec<u8>);
        let mut to_visit: BinaryHeap<Reverse<SEARCH>> = BinaryHeap::new();
        to_visit.push(Reverse((0, Vec::new())));
        while let Some(Reverse((done, vec))) = to_visit.pop() {
            if vec.len() == cond.len() {
                dbg!(vec);
                let ans = to_num(&[3, 0, 6, 2, 3, 4, 6, 3, 1, 2, 2, 0, 4, 2, 3, 3]);
                let mut pc = self.reset(ans);
                pc.run();
                dbg!(&pc.output);
                return ans as usize;
            }
            let base = to_num(&vec);
            for i in 0..7_u8 {
                let cand = base * 8 + i as isize;
                let mut pc = self.reset(cand);
                if compatible(&cond, pc.run()) {
                    let mut v = vec.clone();
                    v.push(i);
                    to_visit.push(Reverse((done + 1, v)));
                }
            }
        }
        'next: for target in cond.iter() {
            let base = to_num(&result);
            for i in 0..7_u8 {
                let cand = base * 8 + i as isize;
                let mut pc = self.reset(cand);
                if compatible(&cond, pc.run()) {
                    result.push(i);
                    dbg!(&result);
                    continue 'next;
                }
            }
            dbg!(&result);
            break;
        }

        // for i in 0..64 {
        //     let mut pc = self.clone();
        //     pc.reg[0] = i;
        //     pc.run();
        //     println!("{i:>2o} {:?}", &pc.output);
        // }
        return 0;
        dbg!(self.code.len());
        let mut digits = 0;
        for i in 2_isize.pow(30)..=2_isize.pow(48) {
            let mut pc = self.clone();
            pc.reg[0] = i;
            pc.run();
            if pc.code == pc.output {
                return i as usize;
            }
            if i % 100 == 0 {
                progress!(format!("{:>2.6}", i as f64 / 2_isize.pow(18) as f64));
            }
            digits = digits.max(pc.output.len());
        }
        digits
        // let mut len = 0;
        /* println!("      {}", &self.input);
        // for i in 2_isize.pow(16)..=2_isize.pow(18) {
        //     let mut pc = self.clone();
        //     pc.reg[0] = i;
        //     pc.run();
        //     println!("{} => {}", i, &pc.output);
        // } */
        /* for i in 0..=64 {
            let mut pc = self.clone();
            pc.reg[0] = i;
            pc.run_breakable();
            println!("{:o}: {:?}", i, pc.output);
            /* if i % 100 == 0 {
                progress!(format!("{:>2.6}", (i as f64).log2()));
            } */
            // println!("{}:{}", i, pc.output.len());
        }
        0 */
    }
}
