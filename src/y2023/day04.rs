//! <https://adventofcode.com/2023/day/4>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    line_parser,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    card: Vec<[Vec<usize>; 2]>,
    amount: Vec<usize>,
}

#[aoc(2023, 4)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let mut vecs: [Vec<usize>; 2] = [Vec::new(), Vec::new()];
        for (i, segment) in block.split(':').nth(1).unwrap().split(" | ").enumerate() {
            vecs[i] = line_parser::to_usizes(segment, ' ').unwrap();
        }
        self.card.push(vecs);
        self.amount.push(1);
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.card
            .iter()
            .map(|[winning, numbers]| {
                let is = winning
                    .iter()
                    .cloned()
                    .filter(|e| numbers.contains(e))
                    .collect::<Vec<_>>();
                match is.len() {
                    0 => 0,
                    1 => 1,
                    n => 2usize.pow(n as u32 - 1),
                }
            })
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        for (i, [winning, numbers]) in self.card.iter().enumerate() {
            let n = winning
                .iter()
                .cloned()
                .filter(|e| numbers.contains(e))
                .count();
            for j in (i + 1)..(i + 1 + n).min(self.card.len()) {
                self.amount[j] += self.amount[i];
            }
        }
        self.amount.iter().sum()
    }
}
