//! <https://adventofcode.com/2019/day/1>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<usize>,
}

#[aoc(2019, 1)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            self.line.push(l.parse::<usize>()?);
        }
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().map(|v| fuel(*v)).sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line.iter().map(|v| fuel2(*v)).sum()
    }
}

fn fuel(mass: usize) -> usize {
    mass / 3 - 2
}

fn fuel2(mass: usize) -> usize {
    let mut f = mass / 3;
    if 2 < f {
        f -= 2;
        f += fuel2(f);
        f
    } else {
        0
    }
}
