//! <https://adventofcode.com/2020/day/15>
#![allow(unused_imports)]
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    dic: HashMap<usize, usize>,
    last: usize,
    clock: usize,
}

#[aoc(2020, 15)]
impl AdventOfCode for Puzzle {
    // const DELIMITER: &'static str = ",";
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        for block in input.split(',') {
            if let Ok(n) = block.trim().parse::<usize>() {
                self.clock += 1;
                *self.dic.entry(n).or_insert(0) = self.clock;
                self.last = n;
            }
        }
        Self::parsed()
    }
    fn part1(&mut self) -> usize {
        self.run_to(2020)
    }
    fn part2(&mut self) -> usize {
        self.run_to(30000000)
    }
}

impl Puzzle {
    fn run_to(&mut self, limit: usize) -> usize {
        self.clock += 1;
        loop {
            let last_entry = self.dic.entry(self.last).or_insert(0);
            if *last_entry == 0 {
                *last_entry = self.clock - 1;
                self.last = 0;
            } else {
                self.last = self.clock - 1 - *last_entry;
                *last_entry = self.clock - 1;
            }
            if limit == self.clock {
                return self.last;
            }
            self.clock += 1;
        }
    }
}
