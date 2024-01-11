//! <https://adventofcode.com/2015/day/4>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    md5::{Digest, Md5},
};

#[derive(Debug, Default)]
pub struct Puzzle {
    line: String,
}

#[aoc(2015, 4)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block.to_string();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        for i in 0.. {
            let mut hasher = Md5::new();
            hasher.update(&format!("{}{}", self.line, i));
            let d = hasher.finalize();
            if d[0] == 0 && d[1] == 0 && d[2] < 16 {
                return i;
            }
        }
        unreachable!()
    }
    fn part2(&mut self) -> Self::Output2 {
        for i in 0.. {
            let mut hasher = Md5::new();
            hasher.update(&format!("{}{}", self.line, i));
            if hasher.finalize().iter().take(3).all(|n| *n == 0) {
                return i;
            }
        }
        unreachable!()
    }
}
