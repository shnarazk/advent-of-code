//! <https://adventofcode.com/2015/day/3>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<char>,
    hash: HashMap<(isize, isize), usize>,
}

#[aoc(2015, 3)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn parse(&mut self, block: String) -> Result<String, ParseError> {
        self.line = block.chars().collect::<Vec<char>>();
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.hash.insert((0, 0), 1);
        let mut pos: (isize, isize) = (0, 0);
        for c in self.line.iter() {
            match *c {
                '^' => pos.0 -= 1,
                'v' => pos.0 += 1,
                '<' => pos.1 -= 1,
                '>' => pos.1 += 1,
                _ => panic!(),
            }
            *self.hash.entry(pos).or_insert(0) += 1;
        }
        self.hash.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.hash.insert((0, 0), 1);
        let mut pos: (isize, isize) = (0, 0);
        for (_, c) in self.line.iter().enumerate().filter(|(i, _)| i % 2 == 0) {
            match *c {
                '^' => pos.0 -= 1,
                'v' => pos.0 += 1,
                '<' => pos.1 -= 1,
                '>' => pos.1 += 1,
                _ => panic!(),
            }
            *self.hash.entry(pos).or_insert(0) += 1;
        }
        let mut pos: (isize, isize) = (0, 0);
        for (_, c) in self.line.iter().enumerate().filter(|(i, _)| i % 2 == 1) {
            match *c {
                '^' => pos.0 -= 1,
                'v' => pos.0 += 1,
                '<' => pos.1 -= 1,
                '>' => pos.1 += 1,
                _ => panic!(),
            }
            *self.hash.entry(pos).or_insert(0) += 1;
        }
        self.hash.len()
    }
}
