//! <https://adventofcode.com/2017/day/5>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
    len: usize,
}

#[aoc(2017, 5)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            self.line.push(l.parse::<isize>()?);
        }
        self.len = self.line.len();
        Ok(())
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
