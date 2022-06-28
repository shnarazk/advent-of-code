//! <https://adventofcode.com/2019/day/6>
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

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(String, String)>,
    orbit: HashSet<(String, String)>,
}

#[aoc(2019, 6)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^(.{3})\)(.{3})$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line
            .push((segment[1].to_string(), segment[2].to_string()));
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
        for (a, b) in self.line.iter() {
            self.orbit.insert((a.clone(), b.clone()));
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut to_visit: Vec<(String, usize)> = vec![("COM".to_string(), 0)];
        let mut count = 0;
        while let Some((target, dist)) = to_visit.pop() {
            count += dist;
            for (_, child) in self.orbit.iter().filter(|(k, _)| *k == target) {
                to_visit.push((child.to_string(), dist + 1));
            }
        }
        count
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
