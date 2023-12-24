//! <https://adventofcode.com/2023/day/23>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{neighbors, Dim2, GeometricMath},
        line_parser, regex,
    },
    std::collections::HashSet,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
}

#[aoc(2023, 23)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.bytes().collect::<Vec<_>>());
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len();
        let width = self.line[0].len();
        let goal = (height - 1, width - 2);
        let mut to_visit: Vec<(Dim2<usize>, HashSet<Dim2<usize>>)> = vec![];
        let mut longest = 0;
        to_visit.push(((0, 1), HashSet::new()));
        while let Some(p) = to_visit.pop() {
            if p.0 == goal {
                longest = dbg!(longest.max(p.1.len()));
                continue;
            }
            for q0 in p.0.neighbors4((0, 0), (height, width)).iter_mut() {
                let mut q = p.clone();
                match self.line[q0.0][q0.1] {
                    b'^' => {
                        q.1.insert(*q0);
                        q0.0 -= 1;
                    }
                    b'<' => {
                        q.1.insert(*q0);
                        q0.1 -= 1;
                    }
                    b'>' => {
                        q.1.insert(*q0);
                        q0.1 += 1;
                    }
                    b'v' => {
                        q.1.insert(*q0);
                        q0.0 += 1;
                    }
                    _ => (),
                }
                if self.line[q0.0][q0.1] != b'#' && !p.1.contains(q0) {
                    q.0 = *q0;
                    q.1.insert(*q0);
                    to_visit.push(q);
                }
            }
        }
        longest
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
