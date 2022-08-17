//! <https://adventofcode.com/2017/day/21>
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

trait Block {
    fn rotate(&self) -> Self;
    fn flip(&self) -> Self;
    fn permutations(&self, index: usize) -> Self;
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Plane2([bool; 4]);

impl Block for Plane2 {
    fn rotate(&self) -> Self {
        Plane2([self.0[2], self.0[0], self.0[3], self.0[1]])
    }
    fn flip(&self) -> Self {
        Plane2([self.0[1], self.0[0], self.0[3], self.0[2]])
    }
    fn permutations(&self, index: usize) -> Self {
        assert!(index < 8);
        let mut p = self.clone();
        for _ in 0..(index >> 1) {
            p = p.rotate();
        }
        if 0 != index & 1 {
            p = p.flip();
        }
        p
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(Vec<u8>, Vec<u8>)>,
}

#[aoc(2017, 21)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^([.#/]+) => ([.#/]+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1]
                .chars()
                .filter(|c| *c != '/')
                .map(|c| c as u8)
                .collect::<Vec<_>>(),
            segment[2]
                .chars()
                .filter(|c| *c != '/')
                .map(|c| c as u8)
                .collect::<Vec<_>>(),
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        for l in self.line.iter() {
            println!(
                "{:?} => {:?}",
                l.0.iter().map(|c| *c as char).collect::<String>(),
                l.1.iter().map(|c| *c as char).collect::<String>(),
            );
        }
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
