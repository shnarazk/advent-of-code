//! <https://adventofcode.com/2017/day/19>
use {
    crate::framework::{aoc_at, AdventOfCode, ParseError},
    std::collections::HashMap,
};

type Location = (isize, isize);

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    map: HashMap<Location, u8>,
}

#[aoc_at(2017, 19)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = usize;
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|line| line.chars().map(|c| c as u8).collect::<Vec<_>>())
            .collect();
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for (j, l) in self.line.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                if *c != b' ' {
                    self.map.insert((j as isize, i as isize), *c);
                }
            }
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        let start_position: Location = {
            let mut l = (0, 0);
            for loc in self.map.keys() {
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
            if self.map.contains_key(&next) {
                to_visit = Some(next);
                continue;
            }
            direction = (direction.1, direction.0);
            next = (p.0 + direction.0, p.1 + direction.1);
            if self.map.contains_key(&next) {
                to_visit = Some(next);
                direction = (next.0 - p.0, next.1 - p.1);
                continue;
            }
            direction = (-direction.0, -direction.1);
            next = (p.0 + direction.0, p.1 + direction.1);
            if self.map.contains_key(&next) {
                to_visit = Some(next);
                continue;
            }
            to_visit = None;
        }
        letters.iter().map(|c| *c as char).collect::<String>()
    }
    fn part2(&mut self) -> Self::Output2 {
        let start_position: Location = {
            let mut l = (0, 0);
            for loc in self.map.keys() {
                if loc.0 == 0 {
                    l = *loc;
                    break;
                }
            }
            l
        };
        let mut to_visit: Option<Location> = Some(start_position);
        let mut direction: Location = (1, 0);
        let mut steps = 0;
        while let Some(p) = to_visit {
            steps += 1;
            let mut next = (p.0 + direction.0, p.1 + direction.1);
            if self.map.contains_key(&next) {
                to_visit = Some(next);
                continue;
            }
            direction = (direction.1, direction.0);
            next = (p.0 + direction.0, p.1 + direction.1);
            if self.map.contains_key(&next) {
                to_visit = Some(next);
                direction = (next.0 - p.0, next.1 - p.1);
                continue;
            }
            direction = (-direction.0, -direction.1);
            next = (p.0 + direction.0, p.1 + direction.1);
            if self.map.contains_key(&next) {
                to_visit = Some(next);
                continue;
            }
            to_visit = None;
        }
        steps
    }
}
