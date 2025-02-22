//! <https://adventofcode.com/2016/day/06>
use {
    crate::framework::{AdventOfCode, ParseError, aoc_at},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
}

#[aoc_at(2016, 6)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = String;
    fn prepare(&mut self, s: &str) -> Result<(), ParseError> {
        self.line = s
            .lines()
            .map(|l| l.chars().map(|c| c as u8).collect())
            .collect();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        (0..self.line[0].len())
            .map(|i| {
                let mut count: HashMap<u8, usize> = HashMap::new();
                for l in self.line.iter() {
                    *count.entry(l[i]).or_insert(0) += 1;
                }
                count.iter().map(|(k, v)| (*v, *k)).max().unwrap().1 as char
            })
            .collect::<String>()
    }
    fn part2(&mut self) -> Self::Output2 {
        (0..self.line[0].len())
            .map(|i| {
                let mut count: HashMap<u8, usize> = HashMap::new();
                for l in self.line.iter() {
                    *count.entry(l[i]).or_insert(0) += 1;
                }
                count.iter().map(|(k, v)| (*v, *k)).min().unwrap().1 as char
            })
            .collect::<String>()
    }
}
