//! <https://adventofcode.com/2015/day/1>
use crate::{
    framework::{aoc_at, AdventOfCode, ParseError},
    line_parser,
};

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    line: Vec<char>,
}

fn floor(vec: &[char]) -> isize {
    match vec.get(0) {
        None => 0,
        Some('(') => 1 + floor(&vec[1..]),
        Some(')') => -1 + floor(&vec[1..]),
        _ => panic!(),
    }
}

fn to_basement(vec: &[char], level: isize) -> isize {
    match vec.get(0) {
        Some('(') => 1 + to_basement(&vec[1..], level + 1),
        Some(')') if level == 0 => 1,
        Some(')') => 1 + to_basement(&vec[1..], level - 1),
        _ => panic!(),
    }
}

#[aoc_at(2015, 1)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = line_parser::to_chars(block)?;
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        floor(&self.line)
    }
    fn part2(&mut self) -> Self::Output2 {
        to_basement(&self.line, 0)
    }
}
