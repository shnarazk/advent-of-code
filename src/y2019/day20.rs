//! <https://adventofcode.com/2019/day/20>
use crate::geometric::neighbors4;
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap, HashSet},
    },
};

type Location = (usize, usize);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    map: HashMap<Location, u8>,
    gate: HashMap<String, Vec<(Location, Location)>>,
    portal: HashMap<Location, Location>,
}

#[derive(Debug, Default, Eq, PartialEq)]
struct State {
    cost: usize,
    current_level: isize,
    location: Location,
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cost.cmp(&other.cost))
    }
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        self.cost.cmp(&other.cost)
    }
}

#[aoc(2019, 20)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c as u8).collect::<Vec<u8>>());
        Ok(())
    }
    fn end_of_data(&mut self) {
        for (y, l) in self.line.iter().enumerate() {
            for (x, c) in l.iter().enumerate() {
                match *c {
                    b' ' => (),
                    _ if b'A' <= *c && *c <= b'Z' => {
                        self.map.insert((y, x), *c);
                        if y == 0 || x == 0 {
                            continue;
                        }
                        if let Some(h) = self.map.get(&(y - 1, x)) {
                            if b'A' <= *h && *h <= b'Z' {
                                let portal_name =
                                    [*h, *c].iter().map(|c| *c as char).collect::<String>();
                                // seek an open passage around.
                                let locs: (Location, Location) = if 2 <= y
                                    && self.line[y - 2][x] == b'.'
                                {
                                    ((y - 1, x), (y - 2, x))
                                } else if y + 1 < self.line.len() && self.line[y + 1][x] == b'.' {
                                    ((y, x), (y + 1, x))
                                } else {
                                    unreachable!()
                                };
                                if portal_name == "AA" {
                                    self.portal.insert((0, 0), locs.1);
                                } else {
                                    self.map.insert(locs.0, b'*');
                                }
                                if portal_name == "ZZ" {
                                    self.portal.insert(locs.1, (0, 0));
                                }
                                self.gate.entry(portal_name).or_default().push(locs);
                            }
                        } else if let Some(h) = self.map.get(&(y, x - 1)) {
                            if b'A' <= *h && *h <= b'Z' {
                                let portal_name =
                                    [*h, *c].iter().map(|c| *c as char).collect::<String>();
                                // seek an open passage around.
                                let locs: (Location, Location) = if 2 <= x
                                    && self.line[y][x - 2] == b'.'
                                {
                                    ((y, x - 1), (y, x - 2))
                                } else if x + 1 < self.line[0].len() && self.line[y][x + 1] == b'.'
                                {
                                    ((y, x), (y, x + 1))
                                } else {
                                    unreachable!()
                                };
                                if portal_name == "AA" {
                                    self.portal.insert((0, 0), locs.1);
                                } else {
                                    self.map.insert(locs.0, b'*');
                                }
                                if portal_name == "ZZ" {
                                    self.portal.insert(locs.1, (0, 0));
                                }
                                self.gate.entry(portal_name).or_default().push(locs);
                            }
                        }
                    }
                    b'.' | b'#' => {
                        self.map.insert((y, x), *c);
                    }
                    _ => unreachable!(),
                }
            }
        }
        for v in self.gate.values().filter(|v| v.len() == 2) {
            self.portal.insert(v[0].0, v[1].1);
            self.portal.insert(v[1].0, v[0].1);
        }
        debug_assert!(self
            .gate
            .iter()
            .all(|(k, v)| v.len() == 2 || ["AA", "ZZ"].contains(&k.as_str())));
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len();
        let width = self.line[0].len();
        let mut to_visit: BinaryHeap<Reverse<(usize, Location)>> = BinaryHeap::new();
        let mut visited: HashSet<Location> = HashSet::new();
        let start = self.gate.get("AA").unwrap()[0].1;
        let goal = self.gate.get("ZZ").unwrap()[0].1;
        to_visit.push(Reverse((0, start)));
        while let Some(Reverse((cost, loc))) = to_visit.pop() {
            if loc == goal {
                return cost;
            }
            visited.insert(loc);
            for next in neighbors4(loc.0, loc.1, height, width).iter() {
                if visited.contains(next) {
                    continue;
                }
                // dbg!(cost);
                match self.map.get(next) {
                    Some(&b'.') => {
                        to_visit.push(Reverse((cost + 1, *next)));
                    }
                    Some(&b'*') => {
                        let warp = self.portal.get(next).unwrap();
                        to_visit.push(Reverse((cost + 1, *warp)));
                    }
                    _ => (),
                }
            }
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        let distance = self.check_portal_distances();
        // cost, level, location
        let mut to_visit: BinaryHeap<Reverse<State>> = BinaryHeap::new();
        let mut visited: HashSet<(Location, isize)> = HashSet::new();
        let start = (0, 0);
        let goal = self.gate.get("ZZ").unwrap()[0].0;
        to_visit.push(Reverse(State {
            cost: 0,
            current_level: 0,
            location: start,
        }));
        while let Some(Reverse(state)) = to_visit.pop() {
            if state.location == goal {
                continue;
            }
            visited.insert((state.location, state.current_level));
            debug_assert!(
                self.map.get(&state.location) == Some(&b'*') || state.location == start,
                "L188: {:?} at {:?}",
                *self.map.get(&state.location).unwrap() as char,
                state.location,
            );
            let warp = *self.portal.get(&state.location).unwrap();
            // println!(
            //     "search from {warp:?} warped from {:?} (current cost {}, level {})",
            //     state.location, state.cost, state.current_level,
            // );
            for ((_, next), (step_cost, flag)) in distance.iter().filter(|(from, _)| from.0 == warp)
            {
                if visited.contains(&(*next, state.current_level + flag)) {
                    continue;
                }
                debug_assert!(self.map.get(next) == Some(&b'*'));
                if *next == goal && state.current_level == 0 {
                    // println!(
                    //     "found the path to goal (cost {}, level {})",
                    //     state.cost + step_cost - 1,
                    //     state.current_level
                    // );
                    return state.cost + step_cost - 1;
                }
                let current_level = state.current_level + flag;
                if 0 <= current_level {
                    to_visit.push(Reverse(State {
                        cost: state.cost + step_cost,
                        current_level,
                        location: *next,
                    }));
                }
            }
        }
        println!("Fail to search");
        0
    }
}

impl Puzzle {
    fn check_portal_distances(&mut self) -> HashMap<(Location, Location), (usize, isize)> {
        let mut table: HashMap<(Location, Location), (usize, isize)> = HashMap::new();
        // find inner boader
        let mut top_left = (0, 0);
        let mut bottom_right = (0, 0);
        let height = self.line.len();
        let width = self.line[0].len();
        'loop1: for y in 2..height {
            for x in 2..width {
                if !self.map.contains_key(&(y, x))
                    && self.map.get(&(y - 1, x - 1)) == Some(&b'#')
                    && self.map.get(&(y - 1, x)) == Some(&b'#')
                    && self.map.get(&(y, x - 1)) == Some(&b'#')
                {
                    top_left = (y, x);
                    break 'loop1;
                }
            }
        }
        'loop2: for y in 2..height {
            for x in 2..width {
                if !self.map.contains_key(&(y, x))
                    && self.map.get(&(y + 1, x + 1)) == Some(&b'#')
                    && self.map.get(&(y + 1, x)) == Some(&b'#')
                    && self.map.get(&(y, x + 1)) == Some(&b'#')
                {
                    bottom_right = (y, x);
                    break 'loop2;
                }
            }
        }
        // dbg!(top_left, bottom_right);
        let inner = move |l: &Location| {
            top_left.0 <= l.0 && l.0 <= bottom_right.0 && top_left.1 <= l.1 && l.1 <= bottom_right.1
        };
        // let goal = self.gate.get("ZZ").unwrap()[0].0;
        for (_, entries) in self.gate.iter() {
            for portal_entry in entries.iter() {
                for (dest, (cost, flag)) in self.build_cost_table(inner, portal_entry.1).iter() {
                    // if name == "AA" {
                    //     dbg!(portal_entry.1, dest, cost);
                    // }
                    if 0 < *cost {
                        debug_assert!(self.map.get(dest) == Some(&b'*'));
                        table.insert((portal_entry.1, *dest), (*cost, *flag));
                        // if goal == *dest {
                        //     println!(
                        //         "to ZZ: {:?} -> {:?}/{}, {}",
                        //         portal_entry.0, dest, cost, flag
                        //     );
                        // }
                    }
                }
            }
        }
        // dbg!(table.len());
        // dbg!(&table
        //     .iter()
        //     // .filter(|((s, e), _)| *s == (2_usize, 53_usize))
        //     .collect::<Vec<_>>());
        table
    }
    fn build_cost_table(
        &self,
        inner: impl Fn(&Location) -> bool,
        start: Location,
    ) -> HashMap<Location, (usize, isize)> {
        let height = self.line.len();
        let width = self.line[0].len();
        let mut table: HashMap<Location, (usize, isize)> = HashMap::new();
        let mut to_visit: BinaryHeap<Reverse<(usize, Location)>> = BinaryHeap::new();
        let mut visited: HashSet<Location> = HashSet::new();
        to_visit.push(Reverse((0, start)));
        while let Some(Reverse((cost, loc))) = to_visit.pop() {
            visited.insert(loc);
            for next in neighbors4(loc.0, loc.1, height, width).iter() {
                if visited.contains(next) {
                    continue;
                }
                visited.insert(*next);
                match self.map.get(next) {
                    Some(&b'.') => {
                        to_visit.push(Reverse((cost + 1, *next)));
                    }
                    Some(&b'*') => {
                        let sgn = if inner(next) { 1 } else { -1 };
                        debug_assert!(self.map.get(next) == Some(&b'*'));
                        table.insert(*next, (cost + 1, sgn));
                    }
                    _ => (),
                }
            }
        }
        table
    }
}
