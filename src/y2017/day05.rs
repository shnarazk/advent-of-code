//! <https://adventofcode.com/2017/day/5>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
    len: usize,
}

#[aoc(2017, 5)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.parse::<isize>()?);
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.len = self.line.len();
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut pc: isize = 0;
        let mut steps: usize = 0;
        while let Some(ptr) = self.line.get(pc as usize) {
            steps += 1;
            let offset = *ptr;
            self.line[pc as usize] += 1;
            pc += offset;
            // println!("{:?}, pc = {}", self.line, pc);
        }
        steps
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut pc: isize = 0;
        let mut steps: usize = 0;
        while let Some(ptr) = self.line.get(pc as usize) {
            steps += 1;
            let offset = *ptr;
            if 3 <= offset {
                self.line[pc as usize] -= 1;
            } else {
                self.line[pc as usize] += 1;
            }
            pc += offset;
        }
        steps
    }
}
