//! <https://adventofcode.com/2018/day/1>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc_at},
        parser,
    },
    std::collections::HashSet,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
}

#[aoc_at(2018, 1)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            self.line.push(parser::to_isize(l)?);
        }
        Ok(())
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
