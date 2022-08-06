//! <https://adventofcode.com/2017/day/5>
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
    len: usize,
}

#[aoc(2017, 5)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.parse::<isize>()?);
        Ok(())
    }
    fn after_insert(&mut self) {
        self.len = self.line.len();
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut pc: isize = 0;
        let mut steps: usize = 0;
        while let Some(ptr) = self.line.get(pc as usize) {
            steps += 1;
            let addr = *ptr;
            self.line[pc as usize] += 1;
            pc += addr;
            // println!("{:?}, pc = {}", self.line, pc);
        }
        steps
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

#[cfg(feature = "y2017")]
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
