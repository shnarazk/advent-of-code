//! <https://adventofcode.com/2023/day/2>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    index: usize,
    result1: usize,
    result2: usize,
}

#[aoc(2023, 2)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.index += 1;
        let x = block
            .split(": ")
            .nth(1)
            .unwrap()
            .split(';')
            .map(|set| {
                let s = set
                    .split(", ")
                    .map(|b| {
                        let c = b.trim().split(' ').collect::<Vec<_>>();
                        match c[1] {
                            "red" => (c[0].to_owned().parse::<usize>().unwrap(), 0, 0),
                            "green" => (0, c[0].to_owned().parse::<usize>().unwrap(), 0),
                            "blue" => (0, 0, c[0].to_owned().parse::<usize>().unwrap()),
                            _ => panic!("cant"),
                        }
                    })
                    .collect::<Vec<_>>();
                s.iter().fold((0, 0, 0), |acc, val| {
                    (acc.0 + val.0, acc.1 + val.1, acc.2 + val.2)
                })
            })
            .collect::<Vec<_>>();
        let maxs = x.iter().fold((0, 0, 0), |acc, val| {
            (acc.0.max(val.0), acc.1.max(val.1), acc.2.max(val.2))
        });
        if maxs.0 <= 12 && maxs.1 <= 13 && maxs.2 <= 14 {
            self.result1 += self.index;
        }
        self.result2 += maxs.0 * maxs.1 * maxs.2;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.result1
    }
    fn part2(&mut self) -> Self::Output2 {
        self.result2
    }
}
