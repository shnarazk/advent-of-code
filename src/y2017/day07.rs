//! <https://adventofcode.com/2017/day/7>
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

#[derive(Debug, Eq, Hash, PartialEq)]
enum Tree {
    Leaf(String, usize),
    Node(String, usize, Vec<String>),
}

#[derive(Debug, Default, Eq, Hash, PartialEq)]
pub struct Puzzle {
    line: Vec<Tree>,
}

#[aoc(2017, 7)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // dqyjg (65)
        let parser1 = regex!(r"^(\w+) \((\d+)\)$");
        // pqtboz (207) -> ayvns, codwosk
        let parser2 = regex!(r"^(\w+) \((\d+)\) -> ((\w+, )+\w+)$");
        if let Some(segment) = parser1.captures(block) {
            self.line.push(Tree::Leaf(
                segment[1].to_string(),
                segment[2].parse::<usize>()?,
            ));
        } else if let Some(segment) = parser2.captures(block) {
            self.line.push(Tree::Node(
                segment[1].to_string(),
                segment[2].parse::<usize>()?,
                segment[3]
                    .split(", ")
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>(),
            ))
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
