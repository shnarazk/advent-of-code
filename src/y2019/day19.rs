//! <https://adventofcode.com/2019/day/19>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{HashMap, VecDeque},
};

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<isize>,
    memory: HashMap<usize, isize>,
    pc: usize,
    r_base: usize,
}

#[aoc(2019, 19)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = line_parser::to_isizes(block, ',')?;
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

impl Puzzle {
    fn initialize(&mut self) {
        self.memory = HashMap::new();
        for (i, v) in self.line.iter().enumerate() {
            self.memory.insert(i, *v);
        }
        self.pc = 0;
        self.r_base = 0;
    }
    fn run(&mut self, inputs: &mut VecDeque<isize>) -> Option<isize> {
        loop {
            let op = self.memory[&self.pc] % 100;
            let immediate: Vec<u8> = {
                let mut v = Vec::new();
                let mut val = self.memory[&self.pc] / 100;
                while 0 < val {
                    v.push((val % 10) as u8);
                    val /= 10;
                }
                v
            };
            macro_rules! deref {
                ($offset: expr) => {{
                    match immediate.get($offset - 1) {
                        Some(0) | None => self.memory[&(self.pc + $offset)] as usize,
                        Some(1) => (self.pc + $offset) as usize,
                        Some(2) => {
                            (self.r_base as isize + self.memory[&(self.pc + $offset)]) as usize
                        }
                        _ => unreachable!(),
                    }
                }};
                ($offset: expr, true) => {{
                    let addr: usize = match immediate.get($offset - 1) {
                        Some(0) | None => self.memory[&(self.pc + $offset)] as usize,
                        Some(1) => self.pc + $offset,
                        Some(2) => {
                            (self.r_base as isize + self.memory[&(self.pc + $offset)]) as usize
                        }
                        _ => unreachable!(),
                    };
                    self.memory.get(&addr).map_or(0, |p| *p)
                }};
            }
            match op {
                1 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    self.memory.insert(dst, op1 + op2);
                    self.pc += 4;
                }
                2 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    self.memory.insert(dst, op1 * op2);
                    self.pc += 4;
                }
                3 => {
                    let dst = deref!(1);
                    if let Some(i) = inputs.pop_front() {
                        self.memory.insert(dst, i);
                    } else {
                        panic!("No more input.");
                    }
                    self.pc += 2;
                }
                4 => {
                    let op1 = deref!(1, true);
                    self.pc += 2;
                    return Some(op1);
                }
                5 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    if 0 != op1 {
                        self.pc = op2 as usize;
                    } else {
                        self.pc += 3;
                    }
                }
                6 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    if 0 == op1 {
                        self.pc = op2 as usize;
                    } else {
                        self.pc += 3;
                    }
                }
                7 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    self.memory.insert(dst, (op1 < op2) as usize as isize);
                    self.pc += 4;
                }
                8 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    self.memory.insert(dst, (op1 == op2) as usize as isize);
                    self.pc += 4;
                }
                9 => {
                    let op1 = deref!(1, true);
                    self.r_base = (self.r_base as isize + op1) as usize;
                    self.pc += 2;
                }
                99 => {
                    break;
                }
                _ => panic!("op: {op} at {}", self.pc),
            }
        }
        None
    }
}

#[cfg(feature = "y2019")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    // #[test]
    // fn test_part1() {
    //     assert_eq!(
    //         Puzzle::solve(Description::TestData("".to_string()), 1),
    //         Answer::Part1(0)
    //     );
    // }
}
