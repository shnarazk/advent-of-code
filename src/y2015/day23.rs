//! <https://adventofcode.com/2015/day/23>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    parser, regex,
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
        let hlf = regex!(r"^hlf ([ab])$");
        let tpl = regex!(r"^tpl ([ab])$");
        let inc = regex!(r"^inc ([ab])$");
        let jmp = regex!(r"^jmp ([+-]?[0-9]+)$");
        let jie = regex!(r"^jie ([ab]), ([+-]?[0-9]+)$");
        let jio = regex!(r"^jio ([ab]), ([+-]?[0-9]+)$");
        if let Ok(segment) = hlf.captures(block).ok_or(ParseError) {
            self.line
                .push(Inst::Hlf(segment[1].chars().next().unwrap() as u8 - b'a'));
        } else if let Ok(segment) = tpl.captures(block).ok_or(ParseError) {
            self.line
                .push(Inst::Tpl(segment[1].chars().next().unwrap() as u8 - b'a'));
        } else if let Ok(segment) = inc.captures(block).ok_or(ParseError) {
            self.line
                .push(Inst::Inc(segment[1].chars().next().unwrap() as u8 - b'a'));
        } else if let Ok(segment) = jmp.captures(block).ok_or(ParseError) {
            self.line.push(Inst::Jmp(parser::to_isize(&segment[1])?));
        } else if let Ok(segment) = jie.captures(block).ok_or(ParseError) {
            self.line.push(Inst::Jie(
                segment[1].chars().next().unwrap() as u8 - b'a',
                parser::to_isize(&segment[2])?,
            ));
        } else if let Ok(segment) = jio.captures(block).ok_or(ParseError) {
            self.line.push(Inst::Jio(
                segment[1].chars().next().unwrap() as u8 - b'a',
                parser::to_isize(&segment[2])?,
            ));
        } else {
            // dbg!(block);
            return Err(ParseError);
        }
        Ok(())
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
                    pc = (pc as isize + o - 1) as usize;
                }
                Inst::Jie(r, o) => {
                    if reg[*r as usize] % 2 == 0 {
                        pc = (pc as isize + o - 1) as usize;
                    }
                }
                Inst::Jio(r, o) => {
                    if reg[*r as usize] == 1 {
                        pc = (pc as isize + o - 1) as usize;
                    }
                }
            }
            pc += 1;
        }
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
                    pc = (pc as isize + o - 1) as usize;
                }
                Inst::Jie(r, o) => {
                    if reg[*r as usize] % 2 == 0 {
                        pc = (pc as isize + o - 1) as usize;
                    }
                }
                Inst::Jio(r, o) => {
                    if reg[*r as usize] == 1 {
                        pc = (pc as isize + o - 1) as usize;
                    }
                }
            }
            pc += 1;
        }
        reg[1]
    }
}
