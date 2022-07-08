//! <https://adventofcode.com/2019/day/16>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
}

#[aoc(2019, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block
            .chars()
            .map(|c| (c as u8 - b'0') as isize)
            .collect::<Vec<isize>>();
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let base_pattern: Vec<isize> = vec![0, 1, 0, -1];
        let mut scratch = self.line.clone();
        for _ in 0..100 {
            for (step, x) in scratch.iter_mut().enumerate() {
                let mut result = 0;
                for (i, p) in self.line.iter().enumerate() {
                    let ptn = base_pattern[((i + 1) / (step + 1)) % 4];
                    result += p * ptn;
                    // print!("{ptn}, ");
                }
                // println!("{:?}", result);
                *x = result;
            }
            for (i, v) in scratch.iter().enumerate() {
                self.line[i] = (*v % 10).abs();
            }
            // println!("{:?}", &self.line);
        }
        println!("{:?}", &self.line[0..8]);
        self.line.iter().take(8).fold(0, |sum, d| sum * 10 + *d) as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut v = Vec::new();
        for _ in 0..10_000 {
            v.append(&mut self.line.clone());
        }
        self.line = v;
        let skip = self.line.iter().take(8).fold(0, |sum, d| sum * 10 + *d) as usize;
        let base_pattern: Vec<isize> = vec![0, 1, 0, -1];
        let mut scratch = self.line.clone();
        for _ in 0..100 {
            for (step, x) in scratch.iter_mut().enumerate() {
                let mut result = 0;
                for (i, p) in self.line.iter().enumerate() {
                    let ptn = base_pattern[((i + 1) / (step + 1)) % 4];
                    result += p * ptn;
                }
                *x = result;
            }
            for (i, v) in scratch.iter().enumerate() {
                self.line[i] = (*v % 10).abs();
            }
        }
        println!("{:?}", &self.line[0..8]);
        self.line
            .iter()
            .skip(skip)
            .take(8)
            .fold(0, |s, d| s * 10 + *d) as usize
    }
}
