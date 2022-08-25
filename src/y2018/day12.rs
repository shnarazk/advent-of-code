//! <https://adventofcode.com/2018/day/12>
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

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<bool>,
    rules: Vec<(Vec<bool>, bool)>,
}

#[aoc(2018, 12)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn header(&mut self, input: String) -> Result<String, ParseError> {
        let parser = regex!(r"^initial state: (.+)\n\n((.|\n)+)$");
        let segment = parser.captures(&input).ok_or(ParseError)?;
        self.line = segment[1].chars().map(|c| c == '#').collect::<Vec<bool>>();
        Ok(segment[2].to_string())
    }
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^([.#]+) => ([.#]+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.rules.push((
            segment[0].chars().map(|c| c == '#').collect::<Vec<bool>>(),
            &segment[1] == "#",
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
        dbg!(&self.rules.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
