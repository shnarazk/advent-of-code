#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::{AdventOfCode, Description, TryParse};
use {lazy_static::lazy_static, regex::Regex, std::collections::HashMap};

#[derive(Debug)]
struct Puzzle {
    line: Vec<usize>,
}

impl AdventOfCode for Puzzle {
    type Segment = usize;
    type Output1 = usize;
    type Output2 = usize;
    const YEAR: usize = 2021;
    const DAY: usize = 1;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Puzzle { line: Vec::new() }
    }
    fn insert(&mut self, object: usize) {
        self.line.push(object);
    }
    fn part1(&mut self) -> usize {
        let mut last = self.line[0];
        let mut count = 0;
        for l in self.line.iter() {
            if last < *l {
                count += 1;
            }
            last = *l;
        }
        count
    }
    fn part2(&mut self) -> usize {
        fn average3(vec: &[usize]) -> usize {
            assert!(2 < vec.len());
            vec[0] + vec[1] + vec[2]
        }
        let mut last = average3(&self.line);
        let mut count = 0;
        for i in 0..self.line.len() - 2 {
            let new = average3(&self.line[i..]);
            if last < new {
                count += 1;
            }
            last = new;
        }
        count
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::solve(&desc, part));
}
