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
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap, HashSet, VecDeque},
    },
};

const ENTRANCE: u8 = b'@';
const OPEN: u8 = b'.';
const WALL: u8 = b'#';

type Location = (usize, usize);

#[derive(Clone, Debug)]
struct State {
    estimate: usize,
    current_cost: usize,
    inventry: Vec<u8>,
}

impl PartialEq for State {
    fn eq(&self, other: &Self) -> bool {
        self.inventry.eq(&other.inventry)
    }
}

impl Eq for State {}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.estimate.partial_cmp(&other.estimate) {
            Some(Ordering::Equal) => self.current_cost.partial_cmp(&other.current_cost),
            result => result,
        }
    }
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.estimate.cmp(&other.estimate) {
            Ordering::Equal => self.current_cost.cmp(&other.current_cost),
            result => result,
        }
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    map: HashMap<Location, u8>,
    location: HashMap<u8, Location>,
    height: usize,
    width: usize,
    keys: Vec<u8>,
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
                if ![OPEN, WALL].contains(c) {
                    self.location.insert(*c, (j, i));
                }
            }
        }
        self.height = self.line.len();
        self.width = self.line[0].len();
        self.keys = self
            .map
            .values()
            .filter(|c| b'a' <= **c && **c <= b'z')
            .copied()
            .collect::<Vec<u8>>();
    }
    fn part1(&mut self) -> Self::Output1 {
        let n_keys = self.keys.len();
        let shortest = 60;
        let mut to_check: BinaryHeap<Reverse<State>> = BinaryHeap::new();
        to_check.push(Reverse(State {
            estimate: n_keys * shortest,
            current_cost: 0,
            inventry: vec![],
        }));
        let mut len = 0;
        while let Some(Reverse(state)) = to_check.pop() {
            if 2600 <= state.current_cost {
                dbg!();
                continue;
            }
            if state.inventry.len() == self.keys.len() {
                return state.current_cost;
            }
            if len < state.inventry.len() {
                len = state.inventry.len();
                println!("{}:{}/{}", len, state.estimate, to_check.len());
            }
            let from = *state.inventry.last().unwrap_or(&ENTRANCE);
            let map = self.build_cost_map(from, &state.inventry);
            for to in self.keys.iter().filter(|k| !state.inventry.contains(k)) {
                if let Some(c) = map.get(to) {
                    let mut inv = state.inventry.clone();
                    inv.sort();
                    inv.push(*to);
                    let e: usize = state.current_cost + c + (n_keys - inv.len()) * shortest;
                    if !to_check
                        .iter()
                        .any(|Reverse(s)| inv == s.inventry && s.estimate < e)
                    {
                        to_check.push(Reverse(State {
                            estimate: e,
                            current_cost: state.current_cost + c,
                            inventry: inv,
                        }));
                    }
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
                if self.map.get(l).map_or_else(
                    || false,
                    |k| {
                        [ENTRANCE, OPEN].contains(k)
                            || (b'a' <= *k && *k <= b'z')
                            || (b'A' <= *k && *k <= b'Z' && inventry.contains(&(*k + b'a' - b'A')))
                    },
                ) && !cost.contains_key(l)
                {
                    cost.insert(*l, c + 1);
                    let k = self.map.get(l).unwrap();
                    if ![OPEN, ENTRANCE].contains(k) {
                        result.insert(*k, c + 1);
                    }
                    to_visit.push_back(*l);
                }
            }
        }
        result
    }
}
