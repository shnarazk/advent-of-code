//! <https://adventofcode.com/2019/day/8>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<u8>,
    width: usize,
    height: usize,
}

#[aoc(2019, 8)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block.chars().map(|c| c as u8 - b'0').collect::<Vec<u8>>();
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        self.width = 25;
        self.height = 6;
        let delta = self.width * self.height;
        let n_layers = self.line.len() / delta;
        let mut target: usize = 0;
        let mut min_zeros: usize = delta;
        for start in (0..n_layers).map(|i| i * delta) {
            let n_zeros = (start..start + delta)
                .filter(|i| self.line[*i] == 0)
                .count();
            if n_zeros < min_zeros {
                min_zeros = n_zeros;
                target = start;
            }
        }
        (target..target + delta)
            .filter(|i| self.line[*i] == 1)
            .count()
            * (target..target + delta)
                .filter(|i| self.line[*i] == 2)
                .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
