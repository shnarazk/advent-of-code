//! <https://adventofcode.com/2018/day/10>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<isize>>,
}

#[aoc(2018, 10)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // position=< 50781, -20123> velocity=<-5,  2>
        let parser = regex!(r"^position=< *(-?\d+), +(-?\d+)> velocity=< *(-?\d+), +(-?\d+)>");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push(vec![
            segment[1].parse::<_>()?,
            segment[2].parse::<_>()?,
            segment[3].parse::<_>()?,
            segment[4].parse::<_>()?,
        ]);
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
