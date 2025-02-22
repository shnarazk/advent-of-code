//! <https://adventofcode.com/2015/day/3>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<char>,
    hash: HashMap<(isize, isize), usize>,
}

#[aoc(2015, 3)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block.chars().collect::<Vec<char>>();
        Ok(())
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
