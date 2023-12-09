//! <https://adventofcode.com/2023/day/9>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    line_parser,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<isize>>,
}

#[aoc(2023, 9)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(line_parser::to_isizes(block, ' ').unwrap());
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().map(extrapolate).sum::<isize>() as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line.iter().map(extrapolate_backword).sum::<isize>() as usize
    }
}

fn extrapolate(vec: &Vec<isize>) -> isize {
    if vec.iter().all(|n| *n == 0) {
        return 0;
    }
    let last = vec.last().unwrap();
    let v = vec.windows(2).map(|p| p[1] - p[0]).collect::<Vec<isize>>();
    *last + extrapolate(&v)
}

fn extrapolate_backword(vec: &Vec<isize>) -> isize {
    if vec.iter().all(|n| *n == 0) {
        return 0;
    }
    let base = vec.first().unwrap();
    let v = vec.windows(2).map(|p| p[1] - p[0]).collect::<Vec<isize>>();
    base - extrapolate_backword(&v)
}
