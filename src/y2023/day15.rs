//! <https://adventofcode.com/2023/day/15>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<String>,
}

#[aoc(2023, 15)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block
            .trim()
            .split(',')
            .map(|s| s.to_string())
            .collect::<Vec<_>>();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|s| {
                s.bytes()
                    .fold(0usize, |ac, x| (17 * (ac + x as usize)) % 256)
            })
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut boxes: Vec<Vec<(&str, usize)>> = (0..256).map(|_| Vec::new()).collect::<Vec<_>>();
        for s in &self.line {
            let remove = s.contains('-');
            let k = (if remove { s.split('-') } else { s.split('=') }).collect::<Vec<_>>();
            let n = k[0]
                .bytes()
                .fold(0usize, |ac, x| (17 * (ac + x as usize)) % 256);
            let found = boxes[n]
                .iter()
                .enumerate()
                .find(|t| *t.1 .0 == *k[0])
                .map(|t| t.0);
            if remove {
                if let Some(i) = found {
                    boxes[n].remove(i);
                }
            } else if let Some(i) = found {
                boxes[n][i].1 = k[1].parse::<usize>().unwrap();
            } else {
                boxes[n].push((k[0], k[1].parse::<usize>().unwrap()));
            }
        }
        boxes
            .iter()
            .enumerate()
            .map(|(n, v)| {
                v.iter()
                    .enumerate()
                    .map(|(i, (_, value))| (n + 1) * (i + 1) * value)
                    .sum::<usize>()
            })
            .sum::<usize>()
    }
}
