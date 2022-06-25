//! <https://adventofcode.com/2019/day/1>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {}

#[aoc(2019, 1)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        println!("This puzzle was solved by Swift.");
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        println!("This puzzle was solved by Swift.");
        0
    }
}
