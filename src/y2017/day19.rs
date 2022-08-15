//! <https://adventofcode.com/2017/day/19>
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

type Location = (isize, isize);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    map: HashMap<Location, u8>,
}

#[aoc(2017, 19)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c as u8).collect::<Vec<_>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        for (j, l) in self.line.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                if *c != b' ' {
                    self.map.insert((j as isize, i as isize), *c);
                }
            }
        }
        dbg!(&self.map.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let start_position: Location = {
            let mut l = (0, 0);
            for (loc, p) in self.map.iter() {
                if loc.0 == 0 {
                    l = *loc;
                    break;
                }
            }
            l
        };
        let mut to_visit: Option<Location> = Some(start_position);
        let mut direction: Location = (1, 0);
        let mut letters: Vec<u8> = Vec::new();
        while let Some(p) = to_visit {
            if let Some(c) = self.map.get(&p) {
                if b'A' <= *c && *c <= b'Z' {
                    letters.push(*c);
                }
            }
            let mut next = (p.0 + direction.0, p.1 + direction.1);
            if self.map.get(&next).is_some() {
                to_visit = Some(next);
                continue;
            }
            direction = (direction.1, direction.0);
            next = (p.0 + direction.0, p.1 + direction.1);
            if self.map.get(&next).is_some() {
                to_visit = Some(next);
                direction = (next.0 - p.0, next.1 - p.1);
                println!("turn");
                continue;
            }
            direction = (-direction.0, -direction.1);
            next = (p.0 + direction.0, p.1 + direction.1);
            if self.map.get(&next).is_some() {
                to_visit = Some(next);
                println!("turn");
                continue;
            }
            to_visit = None;
        }
        println!("{}", letters.iter().map(|c| *c as char).collect::<String>());
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
