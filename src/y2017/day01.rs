//! <https://adventofcode.com/2017/day/1>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<usize>,
}

#[aoc(2017, 1)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block
            .trim()
            .chars()
            .map(|c| (c as u8 - b'0') as usize)
            .collect::<Vec<_>>();
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut data = self.line.clone();
        data.push(data[0]);
        dbg!(
            data.windows(2)
                .filter(|v| v[0] == v[1])
                .map(|v| v[0])
                .sum::<usize>()
        )
    }
    fn part2(&mut self) -> Self::Output2 {
        let len = self.line.len();
        let offset = len / 2;
        let mut result: usize = 0;
        for (i, n) in self.line.iter().enumerate() {
            let t = (i + offset) % len;
            if *n == self.line[t] {
                result += *n;
            }
        }
        result
    }
}
