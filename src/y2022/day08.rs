//! <https://adventofcode.com/2022/day/8>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
    map: HashMap<(usize, usize), usize>,
}

#[aoc(2022, 8)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(
            block
                .chars()
                .map(|c| c as usize - '0' as usize)
                .collect::<Vec<_>>(),
        );
        Ok(())
    }
    fn after_insert(&mut self) {
        for (y, l) in self.line.iter().enumerate() {
            for (x, h) in l.iter().enumerate() {
                self.map.insert((y, x), *h);
            }
        }
        // dbg!(&self.map);
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len();
        let width = self.line[0].len();
        self.map
            .iter()
            .filter(|((y, x), h)| {
                (0..*y).all(|yy| self.map.get(&(yy, *x)).unwrap() < h)
                    || (*y + 1..height).all(|yy| self.map.get(&(yy, *x)).unwrap() < h)
                    || (0..*x).all(|xx| self.map.get(&(*y, xx)).unwrap() < h)
                    || (*x + 1..width).all(|xx| self.map.get(&(*y, xx)).unwrap() < h)
            })
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
