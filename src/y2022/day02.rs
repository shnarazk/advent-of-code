//! <https://adventofcode.com/2022/day/2>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(char, char)>,
}

#[aoc(2022, 2)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|l| {
                let chars = l.chars().collect::<Vec<_>>();
                (chars[0], chars[2])
            })
            .collect::<Vec<_>>();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        #[allow(clippy::identity_op)]
        self.line
            .iter()
            .map(|game| match game {
                ('A', 'X') => 1 + 3,
                ('A', 'Y') => 2 + 6,
                ('A', 'Z') => 3 + 0,
                ('B', 'X') => 1 + 0,
                ('B', 'Y') => 2 + 3,
                ('B', 'Z') => 3 + 6,
                ('C', 'X') => 1 + 6,
                ('C', 'Y') => 2 + 0,
                ('C', 'Z') => 3 + 3,
                _ => unreachable!(),
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        #[allow(clippy::identity_op)]
        self.line
            .iter()
            .map(|game| match game {
                ('A', 'X') => 3 + 0,
                ('A', 'Y') => 1 + 3,
                ('A', 'Z') => 2 + 6,
                ('B', 'X') => 1 + 0,
                ('B', 'Y') => 2 + 3,
                ('B', 'Z') => 3 + 6,
                ('C', 'X') => 2 + 0,
                ('C', 'Y') => 3 + 3,
                ('C', 'Z') => 1 + 6,
                _ => unreachable!(),
            })
            .sum()
    }
}
