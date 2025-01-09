//! <https://adventofcode.com/2018/day/5>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
}

#[aoc(2018, 5)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block
            .chars()
            .map(|c| {
                if c.is_ascii_uppercase() {
                    (c as u8 as isize) - (b'A' as isize) + 1
                } else if c.is_ascii_lowercase() {
                    (b'a' as isize) - (c as u8 as isize) - 1
                } else {
                    panic!();
                }
            })
            .collect::<Vec<isize>>();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.len(0)
    }
    fn part2(&mut self) -> Self::Output2 {
        (1..=26).map(|ex| self.len(ex)).min().unwrap()
    }
}

impl Puzzle {
    fn len(&self, ex: isize) -> usize {
        let mut result = Vec::new();
        for c in self.line.iter() {
            if c.abs() == ex {
                continue;
            }
            if result.last().is_some_and(|l| *l + *c == 0) {
                result.pop();
            } else {
                result.push(*c);
            }
        }
        result.len()
    }
}
