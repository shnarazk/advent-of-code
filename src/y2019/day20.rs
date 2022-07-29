//! <https://adventofcode.com/2019/day/20>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::geometric::neighbors4;
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
    },
    std::{
        cmp::Reverse,
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

#[aoc(2019, 20)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c as u8).collect::<Vec<u8>>());
        Ok(())
    }
    fn after_insert(&mut self) {
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
                                if portal_name != "AA" {
                                    self.map.insert(locs.0, b'*');
                                }
                                self.gate
                                    .entry(portal_name)
                                    .or_insert(Vec::new())
                                    .push(locs);
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
                                if portal_name != "AA" {
                                    self.map.insert(locs.0, b'*');
                                }
                                self.gate
                                    .entry(portal_name)
                                    .or_insert(Vec::new())
                                    .push(locs);
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
        dbg!(&self.map.len());
        dbg!(&self.gate.len());
        assert!(self
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
        dbg!(&start);
        let goal = self.gate.get("ZZ").unwrap()[0].1;
        dbg!(&goal);
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
        self.check_portal_distances();
        0
    }
}

impl Puzzle {
    fn check_portal_distances(&mut self) {
        let mut xs: HashMap<usize, isize> = HashMap::new();
        let mut ys: HashMap<usize, isize> = HashMap::new();
        for (loc, _) in self.map.iter().filter(|(_, kind)| **kind == b'*') {
            *ys.entry(loc.0).or_insert(0) -= 1;
            *xs.entry(loc.1).or_insert(0) -= 1;
        }
        let mut ys = ys.iter().map(|(l, c)| (*l, *c)).collect::<Vec<_>>();
        ys.sort_by_key(|(_, count)| *count);
        let mut xs = xs.iter().map(|(l, c)| (*l, *c)).collect::<Vec<_>>();
        xs.sort_by_key(|(_, count)| *count);
        dbg!(&ys[0..4]);
        dbg!(&xs[0..4]);
        let mut inner_y = ys[0..4].iter().map(|(p, _)| *p).collect::<Vec<_>>();
        inner_y.sort_unstable();
        let mut inner_x = xs[0..4].iter().map(|(p, _)| *p).collect::<Vec<_>>();
        inner_x.sort_unstable();
        let inner = move |l: &Location| {
            (inner_y[1..3].contains(&l.0) && inner_x[1] <= l.1 && l.1 <= inner_x[2])
                || (inner_x[1..3].contains(&l.1) && inner_y[1] <= l.0 && l.0 <= inner_y[2])
        };
        for (name, entries) in self.gate.iter() {
            for portal_entry in entries.iter() {
                for (dest, (cost, flag)) in self.build_cost_table(&inner, portal_entry.1).iter() {
                    if 0 < *cost {
                        println!("{:?} -> {:?}/{}, {}", portal_entry.0, dest, cost, flag);
                    }
                }
            }
        }
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
                        table.insert(*next, (cost, sgn));
                    }
                    _ => (),
                }
            }
        }
        table
    }
}

#[cfg(feature = "y2019")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    // #[test]
    // fn test_part1() {
    //     assert_eq!(
    //         Puzzle::solve(Description::TestData("".to_string()), 1),
    //         Answer::Part1(0)
    //     );
    // }
}
