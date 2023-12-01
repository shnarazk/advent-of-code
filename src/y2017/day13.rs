//! <https://adventofcode.com/2017/day/13>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
}

#[aoc(2017, 13)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^(\d+): (\d+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line
            .push((segment[1].parse::<usize>()?, segment[2].parse::<usize>()?));
        Ok(())
    }
    fn end_of_data(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut severity: usize = 0;
        for (depth, range) in self.line.iter() {
            let cycle: usize = 2 * (*range - 1);
            if *depth % cycle == 0 {
                severity += depth * *range;
            }
        }
        severity
    }
    fn part2(&mut self) -> Self::Output2 {
        'next_challenge: for delay in 0.. {
            for (depth, range) in self.line.iter() {
                let cycle: usize = 2 * (*range - 1);
                if (*depth + delay) % cycle == 0 {
                    continue 'next_challenge;
                }
            }
            return delay;
        }
        0
    }
}
