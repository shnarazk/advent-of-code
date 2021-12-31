//! <https://adventofcode.com/2015/day/23>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        line_parser,
    },
    lazy_static::lazy_static,
    regex::Regex,
};

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Inst {
    Hlf(u8),
    Tpl(u8),
    Inc(u8),
    Jmp(isize),
    Jie(u8, isize),
    Jio(u8, isize),
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Inst>,
}

#[aoc(2015, 23)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        lazy_static! {
            static ref HLF: Regex = Regex::new(r"^hlf ([ab])$").expect("x");
            static ref TPL: Regex = Regex::new(r"^tpl ([ab])$").expect("x");
            static ref INC: Regex = Regex::new(r"^inc ([ab])$").expect("x");
            static ref JMP: Regex = Regex::new(r"^jmp ([+-]?[0-9]+)$").expect("x");
            static ref JIE: Regex = Regex::new(r"^jie ([ab]), ([+-]?[0-9]+)$").expect("x");
            static ref JIO: Regex = Regex::new(r"^jio ([ab]), ([+-]?[0-9]+)$").expect("x");
        }
        if let Ok(segment) = HLF.captures(block).ok_or(ParseError) {
            self.line.push(Inst::Hlf(
                line_parser::to_chars(&segment[1])?[0] as u8 - b'a',
            ));
        } else if let Ok(segment) = TPL.captures(block).ok_or(ParseError) {
            self.line.push(Inst::Tpl(
                line_parser::to_chars(&segment[1])?[0] as u8 - b'a',
            ));
        } else if let Ok(segment) = INC.captures(block).ok_or(ParseError) {
            self.line.push(Inst::Inc(
                line_parser::to_chars(&segment[1])?[0] as u8 - b'a',
            ));
        } else if let Ok(segment) = JMP.captures(block).ok_or(ParseError) {
            self.line
                .push(Inst::Jmp(line_parser::to_isize(&segment[1])?));
        } else if let Ok(segment) = JIE.captures(block).ok_or(ParseError) {
            self.line.push(Inst::Jie(
                line_parser::to_chars(&segment[1])?[0] as u8 - b'a',
                line_parser::to_isize(&segment[2])?,
            ));
        } else if let Ok(segment) = JIO.captures(block).ok_or(ParseError) {
            self.line.push(Inst::Jio(
                line_parser::to_chars(&segment[1])?[0] as u8 - b'a',
                line_parser::to_isize(&segment[2])?,
            ));
        } else {
            dbg!(block);
            return Err(ParseError);
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut reg: [usize; 2] = [0, 0];
        let mut pc = 0;
        while let Some(inst) = self.line.get(pc) {
            // println!("{:>3}: {:?}", pc, inst);
            match inst {
                Inst::Hlf(r) => {
                    reg[*r as usize] /= 2;
                }
                Inst::Tpl(r) => {
                    reg[*r as usize] *= 3;
                }
                Inst::Inc(r) => {
                    reg[*r as usize] += 1;
                }
                Inst::Jmp(o) => {
                    pc += (o - 1) as usize;
                }
                Inst::Jie(r, o) => {
                    if reg[*r as usize] % 2 == 0 {
                        pc += (o - 1) as usize;
                    }
                }
                Inst::Jio(r, o) => {
                    if reg[*r as usize] == 1 {
                        pc += (o - 1) as usize;
                    }
                }
            }
            pc += 1;
        }
        dbg!(&reg);
        reg[1]
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut reg: [usize; 2] = [1, 0];
        let mut pc = 0;
        while let Some(inst) = self.line.get(pc) {
            // println!("{:>3}: {:?}", pc, inst);
            match inst {
                Inst::Hlf(r) => {
                    reg[*r as usize] /= 2;
                }
                Inst::Tpl(r) => {
                    reg[*r as usize] *= 3;
                }
                Inst::Inc(r) => {
                    reg[*r as usize] += 1;
                }
                Inst::Jmp(o) => {
                    pc += (o - 1) as usize;
                }
                Inst::Jie(r, o) => {
                    if reg[*r as usize] % 2 == 0 {
                        pc += (o - 1) as usize;
                    }
                }
                Inst::Jio(r, o) => {
                    if reg[*r as usize] == 1 {
                        pc += (o - 1) as usize;
                    }
                }
            }
            pc += 1;
        }
        dbg!(&reg);
        reg[1]
    }
}
