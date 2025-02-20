//! <https://adventofcode.com/2020/day/1>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    val: Vec<usize>,
}

#[aoc(2020, 1)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn parse_block(&mut self, block: &str) -> Result<(), ParseError> {
        self.val.push(block.parse::<usize>()?);
        Ok(())
    }
    fn part1(&mut self) -> usize {
        for i in &self.val {
            for j in &self.val {
                if i + j == 2020 {
                    return i * j;
                }
            }
        }
        0
    }
    fn part2(&mut self) -> usize {
        for (i, x) in self.val.iter().enumerate() {
            for (j, y) in self.val.iter().enumerate().skip(i) {
                for z in self.val.iter().skip(j) {
                    if x + y + z == 2020 {
                        return x * y * z;
                    }
                }
            }
        }
        0
    }
}
