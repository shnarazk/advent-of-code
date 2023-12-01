//! <https://adventofcode.com/2022/day/1>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    line_parser,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

#[aoc(2022, 1)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(line_parser::to_usizes_spliting_with(block, &['\n'])?);
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().map(|v| v.iter().sum()).max().unwrap()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut elves = self
            .line
            .iter()
            .map(|v| v.iter().sum())
            .collect::<Vec<usize>>();
        // dbg!(&elves);
        elves.sort();
        elves.iter().skip(elves.len() - 3).sum()
    }
}
