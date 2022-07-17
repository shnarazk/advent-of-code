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
    cost_map: HashMap<(u8, u8), usize>,
    requires: HashMap<u8, Vec<u8>>,
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
        self.keys = self
            .map
            .values()
            .filter(|c| b'a' <= **c && **c <= b'z')
            .copied()
            .collect::<Vec<u8>>();
        self.build_cost_map();
        // dbg!(&self.location.len() / 2);
        // dbg!(&self.cost_map);
        // dbg!(&self.requires);
        for key in self.keys.iter() {
            println!(
                "{}: {:?}",
                *key as char,
                self.requires
                    .iter()
                    .filter(|(k, v)| v.contains(key))
                    .map(|(k, _)| *k as char)
                    .collect::<Vec<_>>()
            );
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        let keys = self
            .map
            .values()
            .filter(|c| b'a' <= **c && **c <= b'z')
            .copied()
            .collect::<Vec<u8>>();
        let n_keys = keys.len();
        dbg!(n_keys);
        // Firstly build the initial cost_map
        let shortest = 5;
        let mut to_check: BinaryHeap<Reverse<State>> = BinaryHeap::new();
        to_check.push(Reverse(State {
            estimate: n_keys * shortest,
            current_cost: 0,
            inventry: vec![],
            // cost_map,
        }));
        let mut len = 0;
        while let Some(Reverse(State {
            estimate,
            current_cost,
            inventry,
            // cost_map,
        })) = to_check.pop()
        {
            if inventry.len() == keys.len() {
                dbg!(inventry.iter().map(|c| *c as char).collect::<String>());
                return current_cost;
            }
            if len < inventry.len() {
                len = inventry.len();
                println!("{}:{}", len, to_check.len());
            }
            let now = *inventry.last().unwrap_or(&b'@');
            for next in keys.iter().filter(|k| !inventry.contains(k)) {
                if let Some(c) = self.cost_map.get(&(now, *next)) {
                    let mut inv = inventry.clone();
                    // we should leave only the best (so far) states by dropping old history.
                    inv.sort();
                    inv.push(*next);
                    // let mut map = cost_map.clone();
                    // for k in keys.iter().filter(|k| !inv.contains(k)) {
                    //     if let Some(c) = self.distance(*next, *k, &inv) {
                    //         map.insert((*next, *k), c);
                    //     }
                    // }
                    let mut shortest = usize::MAX;
                    let mut n_path = 0;
                    for from in keys.iter().filter(|k| !inv.contains(k)) {
                        n_path += 1;
                        for to in keys.iter().filter(|k| !inv.contains(k)) {
                            if *from == *to {
                                continue;
                            }
                            if let Some(d) = self.cost_map.get(&(*from, *to)) {
                                if *d < shortest {
                                    shortest = *d;
                                }
                            }
                        }
                    }
                    let e: usize = current_cost + c + n_path * shortest;
                    if !to_check
                        .iter()
                        .any(|Reverse(cngr)| inv == cngr.inventry && cngr.estimate < e)
                    {
                        to_check.push(Reverse(State {
                            estimate: e,
                            current_cost: current_cost + c,
                            inventry: inv,
                            // cost_map: cost_map.clone(), // for now
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
    fn build_cost_map(&mut self) {
        let keys = self
            .map
            .values()
            .filter(|c| b'a' <= **c && **c <= b'z')
            .copied()
            .collect::<Vec<u8>>();
        let mut visited: HashSet<u8> = HashSet::new();
        let mut cost_map: HashMap<(u8, u8), (usize, Vec<u8>)> = HashMap::new();
        let mut new_origin: VecDeque<(u8, Vec<u8>)> = VecDeque::new();
        new_origin.push_back((b'@', Vec::new()));
        while let Some((from, requires)) = new_origin.pop_front() {
            let cost = self.build_cost_map_from(from, &requires);
            let mut cond = requires.clone();
            cond.push(from);
            cond.sort();
            for to in keys.iter() {
                if let Some(d) = cost.get(to) {
                    if visited.contains(to) {
                        continue;
                    }
                    println!(
                        "{}-{}: {}",
                        from as char,
                        *to as char,
                        cond.iter().map(|c| *c as char).collect::<String>()
                    );
                    cost_map.insert((from, *to), (*d, cond.clone()));
                    visited.insert(*to);
                    self.requires.insert(*to, cond.clone());
                    new_origin.push_back((*to, cond.clone()));
                }
            }
        }
        for (p, (d, _)) in cost_map.into_iter() {
            self.cost_map.insert(p, d);
        }
    }
    // This should return not only cost but also requirements,
    // which are the passing keys on the way.
    fn build_cost_map_from(&self, from: u8, inventry: &[u8]) -> HashMap<u8, usize> {
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
}
