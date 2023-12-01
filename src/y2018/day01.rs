//! <https://adventofcode.com/2018/day/1>
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        line_parser,
    },
    std::collections::HashSet,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
}

#[aoc_at(2018, 1)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(line_parser::to_isize(block)?);
        Ok(())
    }
    fn end_of_data(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().copied().sum::<isize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut seen: HashSet<isize> = HashSet::new();
        let mut sum: isize = 0;
        seen.insert(sum);
        for f in self.line.iter().cycle() {
            sum += *f;
            if seen.contains(&sum) {
                return sum;
            }
            seen.insert(sum);
        }
        unreachable!();
    }
}
