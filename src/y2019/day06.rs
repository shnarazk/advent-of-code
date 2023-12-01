//! <https://adventofcode.com/2019/day/6>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
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
    fn end_of_data(&mut self) {
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
        let to_santa = self.path_to("SAN");
        let to_you = self.path_to("YOU");
        for i in 0..to_santa.len().min(to_you.len()) {
            if to_santa[i] != to_you[i] {
                return to_santa.len() + to_you.len() - 2 * i;
            }
        }
        0
    }
}

impl Puzzle {
    fn path_to(&self, target: &str) -> Vec<String> {
        let mut tgt = Some(target);
        let mut path = Vec::new();
        while let Some(ref target) = tgt {
            if let Some((center, _)) = self.orbit.iter().find(|(_, p)| p == target) {
                path.push(center.to_string());
                tgt = Some(center);
            } else {
                tgt = None;
            }
        }
        path.reverse();
        path
    }
}
