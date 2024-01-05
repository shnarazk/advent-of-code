//! <https://adventofcode.com/2015/day/8>
use crate::framework::{aoc, AdventOfCode, ParseError};

fn count(vec: &[char]) -> usize {
    if let Some(ch) = vec.first() {
        match ch {
            '\\' if vec.get(1) == Some(&'\\') => 1 + count(&vec[2..]),
            '\\' if vec.get(1) == Some(&'"') => 1 + count(&vec[2..]),
            '\\' if vec.get(1) == Some(&'x') => 1 + count(&vec[4..]),
            _ => 1 + count(&vec[1..]),
        }
    } else {
        0
    }
}

fn encode(vec: &[char]) -> usize {
    if let Some(ch) = vec.first() {
        match ch {
            '"' => 2 + encode(&vec[1..]),
            '\\' => 2 + encode(&vec[1..]),
            _ => 1 + encode(&vec[1..]),
        }
    } else {
        0
    }
}

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
}

#[aoc(2015, 8)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.chars().collect::<Vec<char>>());
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        // for l in self.line.iter() {
        //     println!("{} = {}",
        //              l.iter().collect::<String>(),
        //              count(&l[1..l.len() - 1]),
        //     );
        // }
        let effective: usize = self.line.iter().map(|v| count(&v[1..v.len() - 1])).sum();
        dbg!(effective);
        self.line.iter().map(|v| v.len()).sum::<usize>() - effective
    }
    fn part2(&mut self) -> Self::Output2 {
        // for l in self.line.iter() {
        //     println!("{} = {}", l.iter().collect::<String>(),encode(l) + 2);
        // }
        let effective: usize = self.line.iter().map(|v| 2 + encode(v)).sum();
        dbg!(effective);
        effective - self.line.iter().map(|v| v.len()).sum::<usize>()
    }
}
