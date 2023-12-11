//! <https://adventofcode.com/2023/day/11>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{neighbors, Dim2},
        line_parser, regex,
    },
    std::collections::HashSet,
};

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
    map: HashSet<Dim2<usize>>,
    trans_y: Vec<usize>,
    trans_x: Vec<usize>,
}

#[aoc(2023, 11)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c == '#').collect::<Vec<_>>());
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.trans_x = self.line[0].iter().map(|_| 1).collect::<Vec<usize>>();
        for (y, l) in self.line.iter().enumerate() {
            let mut found = false;
            for (x, g) in l.iter().enumerate() {
                if *g {
                    self.trans_x[x] = 0;
                    found = true;
                }
            }
            self.trans_y.push(!found as usize);
        }
        // println!("trans y:{:?}, x:{:?}", &self.trans_y1, &self.trans_x1);
        // println!("extended map: {:?}", &self.map);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.scale_up(2);
        self.map
            .iter()
            .map(|p| self.sum_of_distances_from(p))
            .sum::<usize>()
            / 2
    }
    fn part2(&mut self) -> Self::Output2 {
        self.scale_up(1000000);
        self.map
            .iter()
            .map(|p| self.sum_of_distances_from(p))
            .sum::<usize>()
            / 2
    }
}

impl Puzzle {
    fn scale_up(&mut self, scale: usize) {
        let mut index = 0;
        for p in self.trans_y.iter_mut() {
            if *p == 0 {
                *p = index;
                index += 1
            } else {
                *p = 0;
                index += scale;
            }
        }
        index = 0;
        for (i, p) in self.trans_x.iter_mut().enumerate() {
            if *p == 0 {
                *p = index;
                index += 1;
            } else {
                *p = 0;
                index += scale;
            }
        }
        for (y, l) in self.line.iter().enumerate() {
            for (x, g) in l.iter().enumerate() {
                if *g {
                    self.map.insert((self.trans_y[y], self.trans_x[x]));
                }
            }
        }
    }
    fn sum_of_distances_from(&self, pos: &Dim2<usize>) -> usize {
        self.map
            .iter()
            .map(|p| pos.0.abs_diff(p.0) + pos.1.abs_diff(p.1))
            .sum()
    }
}
