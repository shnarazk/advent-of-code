//! <https://adventofcode.com/2015/day/1>
use crate::framework::{AdventOfCode, ParseError, aoc_at};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    line: Vec<char>,
}

fn floor(vec: &[char]) -> isize {
    match vec.first() {
        None => 0,
        Some('(') => 1 + floor(&vec[1..]),
        Some(')') => -1 + floor(&vec[1..]),
        _ => panic!(),
    }
}

fn to_basement(vec: &[char], level: isize) -> isize {
    match vec.first() {
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
    fn prepare(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block.chars().collect::<Vec<char>>();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        floor(&self.line)
    }
    fn part2(&mut self) -> Self::Output2 {
        to_basement(&self.line, 0)
    }
}
