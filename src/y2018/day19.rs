//! <https://adventofcode.com/2018/day/19>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::ops::Index;
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Inst>,
    pc_index: usize,
}

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Inst {
    Addr(usize, usize, usize),
    Addi(usize, usize, usize),
    Mulr(usize, usize, usize),
    Muli(usize, usize, usize),
    Banr(usize, usize, usize),
    Bani(usize, usize, usize),
    Borr(usize, usize, usize),
    Bori(usize, usize, usize),
    Setr(usize, usize, usize),
    Seti(usize, usize, usize),
    Gtir(usize, usize, usize),
    Gtri(usize, usize, usize),
    Gtrr(usize, usize, usize),
    Eqir(usize, usize, usize),
    Eqri(usize, usize, usize),
    Eqrr(usize, usize, usize),
}

impl TryFrom<&str> for Inst {
    type Error = ParseError;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let parser = regex!(r"^(\w{4}) (\d+) (\d+) (\d+)$");
        if let Some(segment) = parser.captures(value) {
            let opr1 = segment[2].parse::<usize>()?;
            let opr2 = segment[3].parse::<usize>()?;
            let opr3 = segment[4].parse::<usize>()?;
            match &segment[1] {
                "addr" => Ok(Inst::Addr(opr1, opr2, opr3)),
                "addi" => Ok(Inst::Addi(opr1, opr2, opr3)),
                "mulr" => Ok(Inst::Mulr(opr1, opr2, opr3)),
                "muli" => Ok(Inst::Muli(opr1, opr2, opr3)),
                "banr" => Ok(Inst::Banr(opr1, opr2, opr3)),
                "bani" => Ok(Inst::Bani(opr1, opr2, opr3)),
                "bori" => Ok(Inst::Bori(opr1, opr2, opr3)),
                "borr" => Ok(Inst::Borr(opr1, opr2, opr3)),
                "setr" => Ok(Inst::Setr(opr1, opr2, opr3)),
                "seti" => Ok(Inst::Seti(opr1, opr2, opr3)),
                "gtir" => Ok(Inst::Gtir(opr1, opr2, opr3)),
                "gtri" => Ok(Inst::Gtri(opr1, opr2, opr3)),
                "gtrr" => Ok(Inst::Gtrr(opr1, opr2, opr3)),
                "eqir" => Ok(Inst::Eqir(opr1, opr2, opr3)),
                "eqri" => Ok(Inst::Eqri(opr1, opr2, opr3)),
                "eqrr" => Ok(Inst::Eqrr(opr1, opr2, opr3)),
                _ => Err(ParseError),
            }
        } else {
            Err(ParseError)
        }
    }
}

impl Index<usize> for Inst {
    type Output = usize;
    fn index(&self, index: usize) -> &Self::Output {
        let v = match self {
            Inst::Addr(o1, o2, o3) => [o1, o2, o3],
            Inst::Addi(o1, o2, o3) => [o1, o2, o3],
            Inst::Mulr(o1, o2, o3) => [o1, o2, o3],
            Inst::Muli(o1, o2, o3) => [o1, o2, o3],
            Inst::Banr(o1, o2, o3) => [o1, o2, o3],
            Inst::Bani(o1, o2, o3) => [o1, o2, o3],
            Inst::Borr(o1, o2, o3) => [o1, o2, o3],
            Inst::Bori(o1, o2, o3) => [o1, o2, o3],
            Inst::Setr(o1, o2, o3) => [o1, o2, o3],
            Inst::Seti(o1, o2, o3) => [o1, o2, o3],
            Inst::Gtir(o1, o2, o3) => [o1, o2, o3],
            Inst::Gtri(o1, o2, o3) => [o1, o2, o3],
            Inst::Gtrr(o1, o2, o3) => [o1, o2, o3],
            Inst::Eqir(o1, o2, o3) => [o1, o2, o3],
            Inst::Eqri(o1, o2, o3) => [o1, o2, o3],
            Inst::Eqrr(o1, o2, o3) => [o1, o2, o3],
        };
        v[index]
    }
}

fn execute<'a, 'b>(
    op: &Inst,
    register: &'a [usize; 6],
    out: &'b mut [usize; 6],
) -> &'b mut [usize; 6] {
    macro_rules! reg {
        ($num: expr) => {{
            register[*$num]
        }};
    }
    macro_rules! set {
        ($num: expr) => {{
            *$num
        }};
    }
    macro_rules! val {
        ($num: expr) => {{
            *$num
        }};
    }
    out[..6].copy_from_slice(&register[..6]);
    assert_eq!(&register, &out);
    match op {
        // addr, addi
        Inst::Addr(o0, o1, o2) => out[set!(o2)] = reg!(o0) + reg!(o1),
        Inst::Addi(o0, o1, o2) => out[set!(o2)] = reg!(o0) + val!(o1),
        // // mulr, muli
        Inst::Mulr(o0, o1, o2) => out[set!(o2)] = reg!(o0) * reg!(o1),
        Inst::Muli(o0, o1, o2) => out[set!(o2)] = reg!(o0) * val!(o1),
        // // banr, bani
        Inst::Banr(o0, o1, o2) => out[set!(o2)] = reg!(o0) & reg!(o1),
        Inst::Bani(o0, o1, o2) => out[set!(o2)] = reg!(o0) & val!(o1),
        // // borr, bori
        Inst::Borr(o0, o1, o2) => out[set!(o2)] = reg!(o0) | reg!(o1),
        Inst::Bori(o0, o1, o2) => out[set!(o2)] = reg!(o0) | val!(o1),
        // // setr, seti
        Inst::Setr(o0, o1, o2) => out[set!(o2)] = reg!(o0),
        Inst::Seti(o0, o1, o2) => out[set!(o2)] = val!(o0),
        // // gtir, gtri, gtrr
        Inst::Gtir(o0, o1, o2) => out[set!(o2)] = (val!(o0) > reg!(o1)) as usize,
        Inst::Gtri(o0, o1, o2) => out[set!(o2)] = (reg!(o0) > val!(o1)) as usize,
        Inst::Gtrr(o0, o1, o2) => out[set!(o2)] = (reg!(o0) > reg!(o1)) as usize,
        // // eqir, eqri, eqrr
        Inst::Eqir(o0, o1, o2) => out[set!(o2)] = (val!(o0) == reg!(o1)) as usize,
        Inst::Eqri(o0, o1, o2) => out[set!(o2)] = (reg!(o0) == val!(o1)) as usize,
        Inst::Eqrr(o0, o1, o2) => out[set!(o2)] = (reg!(o0) == reg!(o1)) as usize,
    }
    out
}

#[aoc(2018, 19)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        dbg!(&block);
        let parser = regex!(r"^#ip (\d)");
        if let Some(segment) = parser.captures(block) {
            self.pc_index = segment[1].parse::<usize>()?;
        } else {
            self.line.push(Inst::try_from(block)?);
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
        dbg!(&self.pc_index);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut register: [usize; 6] = [0; 6];
        let mut work: [usize; 6] = [0; 6];
        while let Some(op) = self.line.get(register[self.pc_index]) {
            execute(op, &register, &mut work);
            std::mem::swap(&mut register, &mut work);
            register[self.pc_index] += 1;
        }
        dbg!(&register);
        register[0]
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
