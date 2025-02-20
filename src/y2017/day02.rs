//! <https://adventofcode.com/2017/day/2>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

#[aoc(2017, 2)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block
            .lines()
            .map(|l| {
                l.split_ascii_whitespace()
                    .map(|t| t.parse::<usize>().unwrap())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        // self.line.push(
        //     block
        //         .split_ascii_whitespace()
        //         .map(|t| t.parse::<usize>().unwrap())
        //         .collect::<Vec<_>>(),
        // );
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|row| {
                row.iter().copied().max().unwrap_or(0) - row.iter().copied().min().unwrap_or(0)
            })
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .map(|row| {
                let mut v = row.clone();
                v.sort_unstable();
                for (i, a) in v.iter().enumerate() {
                    for b in &v[i + 1..] {
                        if b % a == 0 {
                            return b / a;
                        }
                    }
                }
                0
            })
            .sum::<usize>()
    }
}
