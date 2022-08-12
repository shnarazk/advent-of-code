//! <https://adventofcode.com/2017/day/12>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{HashMap, HashSet},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, Vec<usize>)>,
}

#[aoc(2017, 12)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // 41 <-> 1244, 1644
        let parser = regex!(r"^(\d+) <.> ((\d+, )*\d+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1].parse::<usize>()?,
            line_parser::to_usizes(&segment[2], '\t')?,
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut map: HashMap<usize, Vec<usize>> = HashMap::new();
        for (from, tos) in self.line.iter() {
            map.insert(*from, tos.clone());
        }
        let mut linked: HashSet<usize> = HashSet::new();
        linked.insert(0);
        let mut to_visit: Vec<usize> = vec![0];
        while let Some(n) = to_visit.pop() {
            if let Some(tos) = map.get(&n) {
                for to in tos.iter() {
                    if !linked.contains(to) {
                        linked.insert(*to);
                        to_visit.push(*to);
                    }
                }
            }
        }
        linked.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
