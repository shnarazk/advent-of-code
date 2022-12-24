//! <https://adventofcode.com/2022/day/24>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric, line_parser, regex,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, HashSet},
    },
};

type Dim2 = (usize, usize);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
    map: HashMap<Dim2, char>,
    width: usize,
    height: usize,
    start: Dim2,
    goal: Dim2,
    blizzard_r: Vec<Dim2>,
    blizzard_d: Vec<Dim2>,
    blizzard_l: Vec<Dim2>,
    blizzard_u: Vec<Dim2>,
}
impl Puzzle {
    fn is_open(&self, time: usize, position: &Dim2) -> bool {
        self.blizzard_r
            .iter()
            .filter(|(y, _)| *y == position.0)
            .all(|(_, init_x)| (init_x - 1 + time) % self.width + 1 != position.1)
            && self
                .blizzard_d
                .iter()
                .filter(|(_, x)| *x == position.1)
                .all(|(init_y, _)| (init_y - 1 + time) % self.height + 1 != position.0)
            && self
                .blizzard_l
                .iter()
                .filter(|(y, _)| *y == position.0)
                .all(|(_, init_x)| {
                    (init_x - 1 + self.width * time - time) % self.width + 1 != position.1
                })
            && self
                .blizzard_u
                .iter()
                .filter(|(_, x)| *x == position.1)
                .all(|(init_y, _)| {
                    (init_y - 1 + self.height * time - time) % self.height + 1 != position.0
                })
    }
}

#[aoc(2022, 24)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.chars().collect::<Vec<char>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        self.height = self.line.len() - 2;
        self.width = self.line[0].len() - 2;
        self.start.1 = self.line[0]
            .iter()
            .enumerate()
            .find(|(i, c)| **c == '.')
            .unwrap()
            .0;
        self.goal.0 = self.line.len() - 1;
        self.goal.1 = self
            .line
            .last()
            .unwrap()
            .iter()
            .enumerate()
            .find(|(i, c)| **c == '.')
            .unwrap()
            .0;
        for (j, l) in self.line.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                match c {
                    '>' => self.blizzard_r.push((j, i)),
                    'v' => self.blizzard_d.push((j, i)),
                    '<' => self.blizzard_l.push((j, i)),
                    '^' => self.blizzard_u.push((j, i)),
                    _ => (),
                }
                self.map.insert((j, i), *c);
            }
        }
        dbg!(self.blizzard_r.len());
        dbg!(self.blizzard_d.len());
        dbg!(self.blizzard_l.len());
        dbg!(self.blizzard_u.len());
    }
    fn dump(&self) {
        let time = 13;
        dbg!(time);
        for (j, l) in self.line.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                if self.map.get(&(j, i)) == Some(&'#') {
                    print!("#");
                } else if self.is_open(time, &(j, i)) {
                    print!(".");
                } else {
                    print!("*");
                }
            }
            println!();
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        #[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct State {
            expected: usize,
            time: usize,
            position: Dim2,
        }
        let mut to_visit: BinaryHeap<Reverse<State>> = BinaryHeap::new();
        let init = State {
            expected: self.goal.0.abs_diff(self.start.0) + self.goal.1.abs_diff(self.start.1),
            time: 0,
            position: self.start,
        };
        let mut visited: HashSet<State> = HashSet::new();
        to_visit.push(Reverse(init.clone()));
        visited.insert(init);
        while let Some(Reverse(state)) = to_visit.pop() {
            if state.position == self.goal {
                return state.time;
            }
            let time = state.time + 1;
            for next_position in geometric::neighbors4(
                state.position.0,
                state.position.1,
                self.height + 2,
                self.width + 2,
            )
            .iter()
            {
                if self.map.get(next_position) == Some(&'#') {
                    continue;
                }
                if self.is_open(time, next_position) {
                    let next = State {
                        expected: time
                            + self.goal.0.abs_diff(next_position.0)
                            + self.goal.1.abs_diff(next_position.1),
                        time,
                        position: *next_position,
                    };
                    if !visited.contains(&next) {
                        to_visit.push(Reverse(next.clone()));
                        visited.insert(next);
                    }
                }
            }
            if self.is_open(time, &state.position) {
                let next = State {
                    expected: state.expected + 1,
                    time,
                    position: state.position,
                };
                if !visited.contains(&next) {
                    to_visit.push(Reverse(next.clone()));
                    visited.insert(next);
                }
            }
        }
        1
    }
    fn part2(&mut self) -> Self::Output2 {
        let part1 = self.search(0, &self.start, &self.goal);
        let part2 = self.search(part1, &self.goal, &self.start);
        self.search(part2, &self.start, &self.goal)
    }
}
impl Puzzle {
    fn search(&self, start_time: usize, start: &Dim2, goal: &Dim2) -> usize {
        #[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct State {
            expected: usize,
            time: usize,
            position: Dim2,
        }
        let mut to_visit: BinaryHeap<Reverse<State>> = BinaryHeap::new();
        let init = State {
            expected: goal.0.abs_diff(start.0) + goal.1.abs_diff(start.1),
            time: start_time,
            position: *start,
        };
        let mut visited: HashSet<State> = HashSet::new();
        to_visit.push(Reverse(init.clone()));
        visited.insert(init);
        while let Some(Reverse(state)) = to_visit.pop() {
            if state.position == *goal {
                return state.time;
            }
            let time = state.time + 1;
            for next_position in geometric::neighbors4(
                state.position.0,
                state.position.1,
                self.height + 2,
                self.width + 2,
            )
            .iter()
            {
                if self.map.get(next_position) == Some(&'#') {
                    continue;
                }
                if self.is_open(time, next_position) {
                    let next = State {
                        expected: time
                            + goal.0.abs_diff(next_position.0)
                            + goal.1.abs_diff(next_position.1),
                        time,
                        position: *next_position,
                    };
                    if !visited.contains(&next) {
                        to_visit.push(Reverse(next.clone()));
                        visited.insert(next);
                    }
                }
            }
            if self.is_open(time, &state.position) {
                let next = State {
                    expected: state.expected + 1,
                    time,
                    position: state.position,
                };
                if !visited.contains(&next) {
                    to_visit.push(Reverse(next.clone()));
                    visited.insert(next);
                }
            }
        }
        1
    }
}
