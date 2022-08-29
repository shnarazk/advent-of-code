//! <https://adventofcode.com/2018/day/19>
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

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Inst>,
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
#[aoc(2018, 19)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    // fn header(&mut self, input: String) -> Maybe<Option<String>> {
    //     let parser: Regex = Regex::new(r"^(.+)\n\n((.|\n)+)$").expect("wrong");
    //     let segment = parser.captures(input).ok_or(ParseError)?;
    //     for num in segment[1].split(',') {
    //         let _value = num.parse::<usize>()?;
    //     }
    //     Ok(Some(segment[2].to_string()))
    // }
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        dbg!(&block);
        let parser = regex!(r"^#");
        if parser.captures(block).is_none() {
            self.line.push(Inst::try_from(block)?);
        }
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
