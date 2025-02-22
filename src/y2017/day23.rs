//! <https://adventofcode.com/2017/day/23>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashMap,
};

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Val {
    Reg(char),
    Lit(isize),
}

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Inst {
    Set(Val, Val),
    Sub(Val, Val),
    Mul(Val, Val),
    Jnz(Val, Val),
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Inst>,
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
            one_of(|c: char| c.is_ascii_lowercase()).map(Val::Reg),
            parse_isize.map(Val::Lit),
        ))
        .parse_next(s)
    }

    fn parse_inst(s: &mut &str) -> ModalResult<Inst> {
        alt((
            seq!(_: "set ", parse_val, _: " ", parse_val).map(|(a, b)| Inst::Set(a, b)),
            seq!(_: "sub ", parse_val, _: " ", parse_val).map(|(a, b)| Inst::Sub(a, b)),
            seq!(_: "mul ", parse_val, _: " ", parse_val).map(|(a, b)| Inst::Mul(a, b)),
            seq!(_: "jnz ", parse_val, _: " ", parse_val).map(|(a, b)| Inst::Jnz(a, b)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Inst>> {
        separated(1.., parse_inst, newline).parse_next(s)
    }
}

#[aoc(2017, 23)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut processor: Runtime = Runtime::initialize(-1, &self.line);
        loop {
            if let Some(c) = processor.execute() {
                return c;
            }
        }
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut b = 67 * 100 + 100000;
        let c = b + 17000;
        // let mut d = 2;
        // // let e = 2;
        // // let f = 1;
        let mut h = 0;
        loop {
            // println!("{REVERT}B:{b:>8}, D:{d:>8}, E:{e:>8}, F:{f:>8}, H:{h:>8}");
            // //            if d * e == b {
            // //                f = 0;
            // //            }
            // e += 1;
            // if e != b {
            //     continue;
            // }
            // e = b;

            // //            d += 1;
            // //            if d != b {
            // //                // e = 2;
            // //                continue;
            // //            }
            // // d = b;

            // //            if f == 0 {
            // //                h += 1;
            // //            }
            if (2..=((b as f64).sqrt() as usize)).any(|k| b % k == 0) {
                h += 1;
            }

            if c == b {
                break;
            }
            b += 17;
            // d = 2;
            // e = 2;
        }
        h
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
struct Runtime {
    id: usize,
    pc: usize,
    register: HashMap<Val, isize>,
    memory: HashMap<usize, Inst>,
    frequency: usize,
    debug_counter: usize,
}

impl Runtime {
    fn initialize(iid: isize, code: &[Inst]) -> Runtime {
        let mut memory: HashMap<usize, Inst> = HashMap::new();
        for (addr, inst) in code.iter().enumerate() {
            memory.insert(addr, *inst);
        }
        let mut register: HashMap<Val, isize> = HashMap::new();
        if 0 <= iid {
            register.insert(Val::Reg('p'), iid);
        }
        Runtime {
            id: iid as usize,
            pc: 0,
            register,
            memory,
            frequency: 0,
            debug_counter: 0,
        }
    }
    fn get(&self, val: &Val) -> isize {
        match val {
            Val::Lit(n) => *n,
            _ => *self.register.get(val).unwrap_or(&0),
        }
    }
    fn set(&mut self, reg: &Val, val: isize) {
        self.register.insert(*reg, val);
    }
    fn execute(&mut self) -> Option<usize> {
        if let Some(inst) = self.memory.get(&self.pc) {
            let ins = *inst;
            // println!("{:>3} {:?}", self.pc, ins);
            match ins {
                Inst::Set(op1, op2) => {
                    let y = self.get(&op2);
                    self.set(&op1, y);
                }
                Inst::Sub(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    self.set(&op1, x - y);
                }
                Inst::Mul(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    self.set(&op1, x * y);
                    self.debug_counter += 1;
                }
                Inst::Jnz(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    if 0 != x {
                        let n: isize = self.pc as isize + y - 1;
                        assert!(0 <= n);
                        self.pc = n as usize;
                    }
                }
            };
            self.pc += 1;
            None
        } else {
            Some(self.debug_counter)
        }
    }
}
