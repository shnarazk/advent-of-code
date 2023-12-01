//! <https://adventofcode.com/2023/day/1>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
    line2: Vec<Vec<char>>,
}

#[aoc(2023, 1)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.chars().collect::<Vec<_>>());
        let mut b = block.to_owned();
        let subst = [
            ("one", '1'),
            ("two", '2'),
            ("three", '3'),
            ("four", '4'),
            ("five", '5'),
            ("six", '6'),
            ("seven", '7'),
            ("eight", '8'),
            ("nine", '9'),
        ];
        let mut acc: Vec<char> = Vec::new();
        while !b.is_empty() {
            let mut bs = b.chars();
            let mut c = bs.next().unwrap();
            for (r, s) in subst {
                if b.starts_with(r) {
                    c = s;
                    break;
                }
            }
            acc.push(c);
            // Wow, letters can be overlapped!
            b = bs.collect::<String>();
        }
        self.line2.push(acc);
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        sum(&self.line)
    }
    fn part2(&mut self) -> Self::Output2 {
        sum(&self.line2)
    }
}

fn sum(l: &[Vec<char>]) -> usize {
    l.iter()
        .map(|v| {
            let d = v.iter().filter(|c| c.is_digit(10)).collect::<Vec<_>>();
            vec![d[0], d[d.len() - 1]]
                .into_iter()
                .collect::<String>()
                .parse::<usize>()
                .unwrap()
        })
        .sum()
}
