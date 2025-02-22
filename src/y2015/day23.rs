//! <https://adventofcode.com/2015/day/23>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Inst {
    Hlf(u8),
    Tpl(u8),
    Inc(u8),
    Jmp(isize),
    Jie(u8, isize),
    Jio(u8, isize),
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Inst>,
}

mod parser {
    use {
        super::Inst,
        crate::parser::parse_isize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, separated, seq},
        },
    };

    fn parse_inst(s: &mut &str) -> ModalResult<Inst> {
        alt((
            seq!(_: "hlf ", alt(('a', 'b'))).map(|(a,)| Inst::Hlf(a as u8 - b'a')),
            seq!(_: "tpl ", alt(('a', 'b'))).map(|(a,)| Inst::Tpl(a as u8 - b'a')),
            seq!(_: "inc ", alt(('a', 'b'))).map(|(a,)| Inst::Inc(a as u8 - b'a')),
            seq!(_: "jmp ", parse_isize).map(|(a,)| Inst::Jmp(a)),
            seq!(_: "jie ", alt(('a', 'b')), _: ", ", parse_isize)
                .map(|(a, b)| Inst::Jie(a as u8 - b'a', b)),
            seq!(_: "jio ", alt(('a', 'b')), _: ", ", parse_isize)
                .map(|(a, b)| Inst::Jio(a as u8 - b'a', b)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Inst>> {
        separated(1.., parse_inst, newline).parse_next(s)
    }
}

#[aoc(2015, 23)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Self::parsed()
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
