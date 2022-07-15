//! <https://adventofcode.com/2019/day/18>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors4,
        line_parser, regex,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, VecDeque},
    },
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
        dbg!(self.distance(b'@', b'c', &[]));
        dbg!(self.distance(b'@', b'a', &[b'c']));
        dbg!(self.distance(b'@', b'b', &[b'c']));
        dbg!(self.distance(b'@', b'd', &[b'c']));
    }
    fn part1(&mut self) -> Self::Output1 {
        let keys = self
            .map
            .values()
            .filter(|c| b'a' <= **c && **c <= b'z')
            .copied()
            .collect::<Vec<u8>>();
        dbg!(keys.len());
        let mut to_check: BinaryHeap<Reverse<(usize, Vec<u8>)>> = BinaryHeap::new();
        to_check.push(Reverse((0, vec![])));
        let mut len = 0;
        while let Some(Reverse((cost, inventry))) = to_check.pop() {
            if inventry.len() == keys.len() {
                dbg!(inventry.iter().map(|c| *c as char).collect::<String>());
                return cost;
            }
            if len < inventry.len() {
                len = inventry.len();
                dbg!(len);
            }
            let cost_map = self.build_cost_map(*inventry.last().unwrap_or(&b'@'), &inventry);
            for key in keys.iter().filter(|k| !inventry.contains(k)) {
                if let Some(c) = cost_map.get(key) {
                    let mut inv = inventry.clone();
                    inv.push(*key);
                    to_check.push(Reverse((cost + c, inv)));
                }
            }
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

impl Puzzle {
    fn build_cost_map(&self, from: u8, inventry: &[u8]) -> HashMap<u8, usize> {
        let mut cost: HashMap<Location, usize> = HashMap::new();
        let mut result: HashMap<u8, usize> = HashMap::new();
        let mut to_visit: VecDeque<Location> = VecDeque::new();
        let start = *self.location.get(&from).unwrap();
        to_visit.push_back(start);
        cost.insert(start, 0);
        while let Some(loc) = to_visit.pop_front() {
            let c = *cost.get(&loc).unwrap();
            for l in neighbors4(loc.0, loc.1, self.height, self.width).iter() {
                if !self.map.get(l).map_or_else(
                    || false,
                    |k| {
                        [b'.', b'@'].contains(k)
                            || (b'a' <= *k && *k <= b'z')
                            || ((b'A' <= *k && *k <= b'Z')
                                && inventry.contains(&(*k + b'a' - b'A')))
                    },
                ) {
                    continue;
                }
                if !cost.contains_key(l) {
                    cost.insert(*l, c + 1);
                    let k = self.map.get(l).unwrap();
                    if ![b'.', b'@'].contains(k) {
                        result.insert(*k, c + 1);
                    }
                    to_visit.push_back(*l);
                }
            }
        }
        result
    }
    fn distance(&self, from: u8, to: u8, inventry: &[u8]) -> Option<usize> {
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
                    |k| {
                        [b'.', b'@'].contains(k)
                            || (b'a' <= *k && *k <= b'z')
                            || ((b'A' <= *k && *k <= b'Z')
                                && inventry.contains(&(*k + b'a' - b'A')))
                    },
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
