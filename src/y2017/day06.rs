//! <https://adventofcode.com/2017/day/6>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser,
    },
    std::collections::{HashMap, HashSet},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<usize>,
    len: usize,
}

#[aoc(2017, 6)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = parser::to_usizes(input, &['\t', ' '])?;
        self.len = self.line.len();
        Self::parsed()
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
