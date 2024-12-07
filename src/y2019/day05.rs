//! <https://adventofcode.com/2019/day/5>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    parser,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
}

#[aoc(2019, 5)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = parser::to_isizes(block, &[','])?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let input = 1;
        let mut output: Vec<isize> = Vec::new();
        let mut pc = 0;
        loop {
            let op = self.line[pc] % 100;
            let immediate: Vec<bool> = {
                let mut v = Vec::new();
                let mut val = self.line[pc] / 100;
                // dbg!(val);
                while 0 < val {
                    v.push(0 < val % 10);
                    val /= 10;
                }
                v
            };
            // dbg!(&op, &immediate);
            macro_rules! fetch {
                ($offset: expr) => {{
                    if let Some(true) = immediate.get($offset - 1) {
                        self.line[pc + $offset]
                    } else {
                        self.line[self.line[pc + $offset] as usize]
                    }
                }};
                ($offset: expr, true) => {{
                    self.line[pc + $offset] as usize
                }};
            }
            match op {
                1 => {
                    let dst = fetch!(3, true);
                    self.line[dst] = fetch!(1) + fetch!(2);
                    pc += 4;
                }
                2 => {
                    let dst = fetch!(3, true);
                    self.line[dst] = fetch!(1) * fetch!(2);
                    pc += 4;
                }
                3 => {
                    let dst = fetch!(1, true);
                    self.line[dst] = input;
                    pc += 2;
                }
                4 => {
                    let op1 = fetch!(1);
                    output.push(op1);
                    pc += 2;
                }
                99 => {
                    break;
                }
                _ => panic!(),
            }
        }
        *output.last().unwrap() as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        let input = 5;
        let mut output: Vec<isize> = Vec::new();
        let mut pc = 0;
        loop {
            let op = self.line[pc] % 100;
            let immediate: Vec<bool> = {
                let mut v = Vec::new();
                let mut val = self.line[pc] / 100;
                while 0 < val {
                    v.push(0 < val % 10);
                    val /= 10;
                }
                v
            };
            macro_rules! fetch {
                ($offset: expr) => {{
                    if let Some(true) = immediate.get($offset - 1) {
                        self.line[pc + $offset]
                    } else {
                        self.line[self.line[pc + $offset] as usize]
                    }
                }};
                ($offset: expr, true) => {{
                    self.line[pc + $offset] as usize
                }};
            }
            match op {
                1 => {
                    let dst = fetch!(3, true);
                    self.line[dst] = fetch!(1) + fetch!(2);
                    pc += 4;
                }
                2 => {
                    let dst = fetch!(3, true);
                    self.line[dst] = fetch!(1) * fetch!(2);
                    pc += 4;
                }
                3 => {
                    let dst = fetch!(1, true);
                    self.line[dst] = input;
                    pc += 2;
                }
                4 => {
                    let op1 = fetch!(1);
                    output.push(op1);
                    pc += 2;
                }
                5 => {
                    let op1 = fetch!(1);
                    let dst = fetch!(2) as usize;
                    if 0 != op1 {
                        pc = dst;
                    } else {
                        pc += 3;
                    }
                }
                6 => {
                    let op1 = fetch!(1);
                    let dst = fetch!(2) as usize;
                    if 0 == op1 {
                        pc = dst;
                    } else {
                        pc += 3;
                    }
                }
                7 => {
                    let op1 = fetch!(1);
                    let op2 = fetch!(2);
                    let dst = fetch!(3, true);
                    self.line[dst] = (op1 < op2) as usize as isize;
                    pc += 4;
                }
                8 => {
                    let op1 = fetch!(1);
                    let op2 = fetch!(2);
                    let dst = fetch!(3, true);
                    self.line[dst] = (op1 == op2) as usize as isize;
                    pc += 4;
                }
                99 => {
                    break;
                }
                _ => panic!("op: {op} at {pc}"),
            }
        }
        *output.last().unwrap() as usize
    }
}
