//! <https://adventofcode.com/2016/day/22>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::usize;

use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{binary_heap::BinaryHeap, HashSet},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, usize, usize, usize, usize, usize)>,
}

#[aoc(2016, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn header(&mut self, input: String) -> Result<String, ParseError> {
        let parser = regex!(r"^.+\n.+\n((.|\n)+)$");
        let segment = parser.captures(&input).ok_or(ParseError)?;
        Ok(segment[1].to_string())
    }
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"/dev/grid/node-x(\d+)-y(\d+) +(\d+)T +(\d+)T +(\d+)T +(\d+)%$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1].parse::<usize>()?,
            segment[2].parse::<usize>()?,
            segment[3].parse::<usize>()?,
            segment[4].parse::<usize>()?,
            segment[5].parse::<usize>()?,
            segment[6].parse::<usize>()?,
        ));
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.sort_unstable_by_key(|line| line.4);
        let n = self.line.len();
        let mut count = 0;
        for (i, dev) in self.line.iter().enumerate() {
            for (j, other) in self.line.iter().enumerate() {
                if 0 < dev.3 && i != j && dev.3 <= other.4 {
                    count += 1;
                }
            }
        }
        count
    }
    fn part2(&mut self) -> Self::Output2 {
        type State = Vec<usize>;
        let mut w = 0;
        let mut h = 0;
        for cell in self.line.iter() {
            w = w.max(cell.0);
            h = h.max(cell.1);
        }
        let width = w + 1;
        let height = h + 1;
        dbg!(width, height);
        assert_eq!(width * height, self.line.len());
        let mut to_visit: BinaryHeap<(usize, usize, State, usize)> = BinaryHeap::new();
        let mut visited: HashSet<State> = HashSet::new();
        let init = self.line.iter().map(|site| site.3).collect::<Vec<usize>>();
        to_visit.push((0, 0, init, width - 1));
        let mut check = width;
        while let Some(state) = to_visit.pop() {
            assert!(visited.len() < 1_000_000);
            if 0 == state.3 {
                dbg!(state.1);
                return 0;
            }
            let mut empty = 0;
            for (i, used) in state.2.iter().enumerate() {
                if *used == 0 {
                    empty = i;
                    break;
                }
            }
            let a_star = state.3 % width + state.3 / width;
            if a_star < check {
                dbg!(a_star);
                check = a_star;
            }
            // Up
            if width <= empty && state.2[empty - width] < self.line[empty].2 {
                let mut new = state.2.clone();
                new.swap(empty, empty - width);
                if !visited.contains(&new) {
                    to_visit.push((
                        state.0 + a_star,
                        state.0 + 1,
                        new,
                        if empty - width == state.3 {
                            empty
                        } else {
                            state.3
                        },
                    ));
                }
            };
            // Down
            if empty + width < self.line.len() && state.2[empty + width] < self.line[empty].2 {
                let mut new = state.2.clone();
                new.swap(empty, empty + width);
                if !visited.contains(&new) {
                    to_visit.push((
                        state.0 + a_star,
                        state.0 + 1,
                        new,
                        if empty + width == state.3 {
                            empty
                        } else {
                            state.3
                        },
                    ));
                }
            };
            // Left
            if 0 < empty % width && state.2[empty - 1] < self.line[empty].2 {
                let mut new = state.2.clone();
                new.swap(empty, empty - 1);
                if !visited.contains(&new) {
                    to_visit.push((
                        state.0 + a_star,
                        state.0 + 1,
                        new,
                        if empty - 1 == state.3 { empty } else { state.3 },
                    ));
                }
            };
            // Right
            if 0 < (empty + 1) % width && state.2[empty + 1] < self.line[empty].2 {
                let mut new = state.2.clone();
                new.swap(empty, empty + 1);
                if !visited.contains(&new) {
                    to_visit.push((
                        state.0 + a_star,
                        state.0 + 1,
                        new,
                        if empty + 1 == state.3 { empty } else { state.3 },
                    ));
                }
            };
            visited.insert(state.2);
        }
        0
    }
}
