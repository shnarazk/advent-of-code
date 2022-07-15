//! <https://adventofcode.com/2019/day/18>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::geometric::neighbors4;
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{HashMap, VecDeque},
};

type Location = (usize, usize);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    map: HashMap<Location, u8>,
    location: HashMap<u8, Location>,
    height: usize,
    width: usize,
}

#[aoc(2019, 18)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c as u8).collect::<Vec<u8>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        for (j, v) in self.line.iter().enumerate() {
            for (i, c) in v.iter().enumerate() {
                self.map.insert((j, i), *c);
                if ![b'.', b'#'].contains(c) {
                    self.location.insert(*c, (j, i));
                }
            }
        }
        self.height = self.line.len();
        self.width = self.line[0].len();
        // dbg!(self.line.len());
        dbg!(&self.location.len() / 2);
        dbg!(self.distance(b'@', b'a', &[]));
        dbg!(self.distance(b'@', b'b', &[]));
        dbg!(self.distance(b'@', b'c', &[]));
        dbg!(self.distance(b'@', b'p', &[]));
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

impl Puzzle {
    fn distance(&self, from: u8, to: u8, inventy: &[u8]) -> Option<usize> {
        let mut cost: HashMap<Location, usize> = HashMap::new();
        let mut to_visit: VecDeque<Location> = VecDeque::new();
        let start = *self.location.get(&from).unwrap();
        let goal = *self.location.get(&to).unwrap();
        to_visit.push_back(start);
        cost.insert(start, 0);
        while let Some(loc) = to_visit.pop_front() {
            let c = *cost.get(&loc).unwrap();
            if loc == goal {
                return Some(c);
            }
            for l in neighbors4(loc.0, loc.1, self.height, self.width).iter() {
                if !self.map.get(l).map_or_else(
                    || false,
                    |k| *k == b'.' || (b'a' <= *k && *k <= b'z') || inventy.contains(k),
                ) {
                    continue;
                }
                if !cost.contains_key(l) {
                    cost.insert(*l, c + 1);
                    to_visit.push_back(*l);
                }
            }
        }
        None
    }
}
