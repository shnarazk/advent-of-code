//! <https://adventofcode.com/2017/day/6>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        line_parser,
    },
    std::collections::{HashMap, HashSet},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<usize>,
    len: usize,
}

#[aoc(2017, 6)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = line_parser::to_usizes(block, '\n')?;
        Ok(())
    }
    fn after_insert(&mut self) {
        self.len = self.line.len();
        dbg!(self.len);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut visited: HashSet<Vec<usize>> = HashSet::new();
        for step in 1_usize.. {
            let mut target = 0;
            let mut nblocks = 0;
            for (i, nb) in self.line.iter().enumerate() {
                if nblocks < *nb {
                    target = i;
                    nblocks = *nb;
                }
            }
            self.line[target] = 0;
            for n in 0..nblocks {
                self.line[(target + n + 1) % self.len] += 1;
            }
            if visited.contains(&self.line) {
                return step;
            }
            visited.insert(self.line.clone());
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut visited: HashMap<Vec<usize>, usize> = HashMap::new();
        visited.insert(self.line.clone(), 0);
        for step in 1_usize.. {
            let mut target = 0;
            let mut nblocks = 0;
            for (i, nb) in self.line.iter().enumerate() {
                if nblocks < *nb {
                    target = i;
                    nblocks = *nb;
                }
            }
            self.line[target] = 0;
            for n in 0..nblocks {
                self.line[(target + n + 1) % self.len] += 1;
            }
            if let Some(past) = visited.get(&self.line) {
                return step - past;
            }
            visited.insert(self.line.clone(), step);
        }
        0
    }
}
