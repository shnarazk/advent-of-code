//! <https://adventofcode.com/2022/day/22>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashSet,
};

type Dim2 = (usize, usize);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    map: HashSet<Dim2>,
    loaded_map: Vec<Vec<char>>,
    line: Vec<Vec<char>>,
}

#[aoc(2022, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let v = block.chars().collect::<Vec<_>>();
        if v.iter().any(|c| [' ', '.', '#'].contains(c)) {
            self.line.push(v);
        } else {
            self.loaded_map.push(v);
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        for (j, l) in self.loaded_map.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                if *c == '.' {
                    self.map.insert((j, i));
                }
            }
        }
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        1
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
