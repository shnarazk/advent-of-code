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
        let site = (
            segment[2].parse::<usize>()?, // y
            segment[1].parse::<usize>()?, // x
            segment[3].parse::<usize>()?,
            segment[4].parse::<usize>()?,
            segment[5].parse::<usize>()?,
            segment[6].parse::<usize>()?,
        );
        self.line.push(site);
        // if 17 != site.0 && 100 < site.2.min(site.3) {
        //     dbg!(site);
        // }
        if 0 == site.3 {
            dbg!(site);
        }
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
        self.line.sort_unstable();
        for cell in self.line.iter() {
            h = h.max(cell.0);
            w = w.max(cell.1);
        }
        let width = w + 1;
        let height = h + 1;
        dbg!(width, height);
        // for (i, cell) in self.line.iter().enumerate() {
        //     print!("{:>3},", cell.2);
        //     if (i + 1) % width == 0 {
        //         println!();
        //     }
        // }
        // if 0 < self.line.len() {
        //     return 0;
        // }
        assert_eq!(width * height, self.line.len());
        let mut to_visit: BinaryHeap<(isize, usize, State, usize)> = BinaryHeap::new();
        let mut visited: HashSet<State> = HashSet::new();
        let init = self.line.iter().map(|site| site.3).collect::<Vec<usize>>();
        dbg!(&init);
        let mut check: isize = -1_000_000;
        to_visit.push((check + 1, 0, init, width - 1));
        while let Some(state) = to_visit.pop() {
            // if 267 <= state.1 {
            //     continue;
            // }
            assert!(visited.len() < 1_000_000);
            let mut empty = 0;
            for (i, used) in state.2.iter().enumerate() {
                if *used == 0 {
                    empty = i;
                    break;
                }
            }
            if (/* 2 < empty / width */check < -170 && check < state.0 + state.1 as isize)
                || 0 == state.3
            {
                for (i, c) in state.2.iter().enumerate() {
                    if i == state.3 {
                        print!(" G ,");
                    } else if *c == 0 {
                        print!(" _ ,");
                    } else {
                        print!("{:>3},", *c);
                    }
                    if (i + 1) % width == 0 {
                        println!();
                    }
                }
                check = state.0 + state.1 as isize;
                dbg!(check, visited.len());
            }
            if 0 == state.3 {
                dbg!(state.1);
                return 0;
            }
            let mut neighbors: Vec<(usize, Vec<usize>)> = Vec::new();
            // Up
            if width <= empty && state.2[empty - width] <= self.line[empty].2 {
                let mut new = state.2.clone();
                new.swap(empty, empty - width);
                if !visited.contains(&new) {
                    neighbors.push((empty - width, new));
                }
            };
            // Down
            if empty + width < self.line.len() && state.2[empty + width] <= self.line[empty].2 {
                let mut new = state.2.clone();
                new.swap(empty, empty + width);
                if !visited.contains(&new) {
                    neighbors.push((empty + width, new));
                }
            };
            // Left
            if 0 < empty % width && state.2[empty - 1] <= self.line[empty].2 {
                let mut new = state.2.clone();
                new.swap(empty, empty - 1);
                if !visited.contains(&new) {
                    neighbors.push((empty - 1, new));
                }
            };
            // Right
            if 0 < (empty + 1) % width && state.2[empty + 1] <= self.line[empty].2 {
                let mut new = state.2.clone();
                new.swap(empty, empty + 1);
                if !visited.contains(&new) {
                    neighbors.push((empty + 1, new));
                }
            };
            while let Some((index, neighbor)) = neighbors.pop() {
                let goal = if index == state.3 { empty } else { state.3 };
                let a_star = if 17 < index / width
                /* && 1 < index % width */
                {
                    10000 + ((index % width).abs_diff(1) + (index / width).abs_diff(0))
                } else if 2 < index / width {
                    1000 + ((index % width).abs_diff((goal % width).saturating_sub(1))
                        + (index / width).abs_diff(goal / width + 1))
                } else {
                    // 2 * (goal % width + goal / width) + (index % width + index / width)
                    3 * (goal % width) + (index % width)
                    // + (index % width).abs_diff(0)
                    // + (index / width).abs_diff(0)
                    // + ((index % width).abs_diff((goal % width).saturating_sub(1)) + (index / width).abs_diff(goal / width))
                };
                to_visit.push((
                    -((state.1 + 1 + a_star) as isize),
                    state.1 + 1,
                    neighbor,
                    goal,
                ));
            }
            visited.insert(state.2);
        }
        0
    }
}
