//! <https://adventofcode.com/2018/day/15>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
    },
    std::collections::HashSet,
};

type Dim2 = (isize, isize);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    map: HashSet<Dim2>,
    goblins: HashSet<Dim2>,
    elves: HashSet<Dim2>,
}

#[aoc(2018, 15)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c as u8).collect::<Vec<u8>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        for (j, l) in self.line.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                let pos = (j as isize, i as isize);
                if *c != b'#' {
                    self.map.insert(pos);
                }
                match *c {
                    b'G' => {
                        self.goblins.insert(pos);
                    }
                    b'E' => {
                        self.elves.insert(pos);
                    }
                    _ => (),
                }
            }
        }
        dbg!(self.goblins.len(), self.elves.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
