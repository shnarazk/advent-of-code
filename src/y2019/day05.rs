//! <https://adventofcode.com/2019/day/5>
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
    line: Vec<isize>,
}

#[aoc(2019, 5)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = line_parser::to_isizes(block, ',')?;
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut pc = 0;
        loop {
            match self.line[pc] {
                1 => {
                    let op1 = self.line[pc + 1];
                    let op2 = self.line[pc + 2];
                    let op3 = self.line[pc + 3];
                    self.line[op3 as usize] = self.line[op1 as usize] + self.line[op2 as usize];
                    pc += 4;
                }
                2 => {
                    let op1 = self.line[pc + 1];
                    let op2 = self.line[pc + 2];
                    let op3 = self.line[pc + 3];
                    self.line[op3 as usize] = self.line[op1 as usize] * self.line[op2 as usize];
                    pc += 4;
                }
                3 => {
                    let op1 = self.line[pc + 1];
                    self.line[op1 as usize] = op1;
                    pc += 2;
                }
                4 => {
                    let op1 = self.line[pc + 1];
                    dbg!(op1);
                    pc += 2;
                }
                99 => {
                    break;
                }
                _ => panic!(),
            }
        }
        dbg!(self.line[0]) as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
