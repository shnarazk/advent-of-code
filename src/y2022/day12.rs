//! <https://adventofcode.com/2022/day/12>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::collections::HashSet;

use crate::geometric;
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap},
    },
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
    start: (usize, usize),
    goal: (usize, usize),
    width: usize,
    height: usize,
}

#[derive(Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct State {
    cost: usize,
    location: (usize, usize),
}

#[aoc(2022, 12)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(
            block
                .chars()
                .map(|c| match c {
                    'S' => 1000,
                    'E' => 2000,
                    _ => c as usize - 'a' as usize,
                })
                .collect::<Vec<_>>(),
        );
        Ok(())
    }
    fn after_insert(&mut self) {
        for (j, l) in self.line.iter().enumerate() {
            for (i, h) in l.iter().enumerate() {
                match h {
                    1000 => self.start = (j, i),
                    2000 => self.goal = (j, i),
                    _ => (),
                }
            }
        }
        self.height = self.line.len();
        self.width = self.line[0].len();
        self.line[self.start.0][self.start.1] = 0;
        self.line[self.goal.0][self.goal.1] = 'z' as usize - 'a' as usize;
        dbg!(&self.goal);
        dbg!(self.height, self.width);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut to_visit: BinaryHeap<Reverse<State>> = BinaryHeap::new();
        let mut visited: HashSet<(usize, usize)> = HashSet::new();
        to_visit.push(Reverse(State {
            cost: 0,
            location: self.start,
        }));
        visited.insert(self.start);
        let mut level = 0;
        let mut steps = 0;
        while let Some(Reverse(state)) = to_visit.pop() {
            if state.location == self.goal {
                return state.cost;
            }
            let lv = self.line[state.location.0][state.location.1];
            if level < lv {
                level = lv;
                steps = state.cost;
            }
            for next in
                geometric::neighbors4(state.location.0, state.location.1, self.height, self.width)
                    .into_iter()
            {
                if self.line[state.location.0][state.location.1] + 1 < self.line[next.0][next.1] {
                    continue;
                }
                if visited.contains(&next) {
                    continue;
                }
                let ns = State {
                    cost: state.cost + 1,
                    location: next,
                };
                to_visit.push(Reverse(ns));
                visited.insert(next);
            }
        }
        for j in 0..self.height {
            for i in 0..self.width {
                print!(
                    "{}",
                    if visited.contains(&(j, i)) {
                        '#'
                    } else {
                        (self.line[j][i] as u8 + b'a') as char
                    }
                )
            }
            println!();
        }
        dbg!(visited.len());
        steps
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut to_visit: BinaryHeap<Reverse<State>> = BinaryHeap::new();
        let mut visited: HashSet<(usize, usize)> = HashSet::new();
        to_visit.push(Reverse(State {
            cost: 0,
            location: self.goal,
        }));
        visited.insert(self.goal);
        while let Some(Reverse(state)) = to_visit.pop() {
            if self.line[state.location.0][state.location.1] == 0 {
                return state.cost;
            }
            let lv = self.line[state.location.0][state.location.1];
            for next in
                geometric::neighbors4(state.location.0, state.location.1, self.height, self.width)
                    .into_iter()
            {
                if self.line[next.0][next.1] + 1 < self.line[state.location.0][state.location.1] {
                    continue;
                }
                if visited.contains(&next) {
                    continue;
                }
                let ns = State {
                    cost: state.cost + 1,
                    location: next,
                };
                to_visit.push(Reverse(ns));
                visited.insert(next);
            }
        }
        unreachable!()
    }
}
