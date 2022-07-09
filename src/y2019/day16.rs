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
    line: Vec<i32>,
}

#[aoc(2019, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block
            .chars()
            .map(|c| (c as u8 - b'0') as i32)
            .collect::<Vec<i32>>();
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let base_pattern: Vec<i32> = vec![0, 1, 0, -1];
        let mut scratch = self.line.clone();
        for _ in 0..100 {
            for (j, x) in scratch.iter_mut().enumerate() {
                let mut result = 0;
                for (i, p) in self.line.iter().enumerate() {
                    let ptn = base_pattern[((i + 1) / (j + 1)) % 4];
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
        let mut v = self.line.clone();
        for _ in 0..10_000 {
            v.append(&mut self.line.clone());
        }
        self.line = v;
        let len = self.line.len();
        let skip = self.line.iter().take(8).fold(0, |sum, d| sum * 10 + *d) as usize;
        assert!(self.line.len() < 2 * skip);
        self.line.iter_mut().for_each(|p| *p = 0);
        for i in skip..len {
            let mut sum = 0;
            for j in i..len {
                sum += self.line[j];
            }
        }

        0
    }
}

impl Puzzle {
    fn part4(&mut self) -> usize {
        let mut v = self.line.clone();
        for _ in 0..10_000 {
            v.append(&mut self.line.clone());
        }
        self.line = v;
        let skip = self.line.iter().take(8).fold(0, |sum, d| sum * 10 + *d) as usize;
        assert!(self.line.len() < 2 * skip);
        self.line.iter_mut().for_each(|p| *p = 0);
        const PATTERN: [i32; 4] = [0, 1, 0, -1];
        let factor = |i: usize, j: usize| PATTERN[((i + 1) / (j + 1)) % 4];
        let mut tmp = self.line.clone();
        self.line[0] = 1;
        for rep in 0..10 {
            tmp.iter_mut().for_each(|p| *p = 0);
            for (j, x) in self.line.iter().enumerate().filter(|(_, p)| **p != 0) {
                for (i, p) in tmp.iter_mut().enumerate() {
                    match PATTERN[((i + 1) / (j + 1)) % 4] {
                        0 => (),
                        _ => *p = 1,
                    }
                }
                print!("\x1B[1A\x1B[1G");
                println!("{}/{}", j, self.line.len());
            }
            std::mem::swap(&mut self.line, &mut tmp);
        }
        dbg!(self.line.iter().filter(|p| **p == 1).count() as f64 / self.line.len() as f64);
        0
    }
    fn part3(&mut self) -> usize {
        let mut v = self.line.clone();
        for _ in 0..10_000 {
            v.append(&mut self.line.clone());
        }
        self.line = v;
        let skip = self.line.iter().take(8).fold(0, |sum, d| sum * 10 + *d) as usize;
        const PATTERN: [i32; 4] = [0, 1, 0, -1];
        let mut scratch = self.line.clone();
        for step in 0..100 {
            dbg!(step);
            for (j, x) in scratch.iter_mut().enumerate() {
                let mut result = 0;
                for (i, p) in self.line.iter().enumerate() {
                    match PATTERN[((i + 1) / (j + 1)) % 4] {
                        -1 => result -= p,
                        1 => result += p,
                        _ => (),
                    }
                }
                *x = (result % 10).abs();
            }
            std::mem::swap(&mut self.line, &mut scratch);
        }
        println!("{:?}", &self.line[0..8]);
        self.line
            .iter()
            .skip(skip)
            .take(8)
            .fold(0, |sum, d| sum * 10 + *d) as usize
    }
}
