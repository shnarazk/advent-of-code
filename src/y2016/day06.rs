//! <https://adventofcode.com/2016/day/06>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::process::Command,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<()>,
}

#[aoc(2016, 6)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        if let Ok(output) = Command::new("bqn/2016/day06.bqn").output() {
            println!("{}", String::from_utf8_lossy(&output.stdout));
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
