//! <https://adventofcode.com/2016/day/18>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<bool>,
}

#[aoc(2016, 18)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, s: &str) -> Result<(), ParseError> {
        self.line = s.trim().chars().map(|c| c == '^').collect::<Vec<_>>();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut work = self.line.clone();
        let mut count = self.line.iter().filter(|b| !**b).count();
        for _ in 1..40 {
            for (i, t) in work.iter_mut().enumerate() {
                let left = i.checked_sub(1).map(|i| self.line[i]).unwrap_or(false);
                let right = *self.line.get(i + 1).unwrap_or(&false);
                *t = left != right;
            }
            std::mem::swap(&mut self.line, &mut work);
            count += self.line.iter().filter(|b| !**b).count();
        }
        count
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut work = self.line.clone();
        let mut count = self.line.iter().filter(|b| !**b).count();
        // FIXME: It may become a dead state or a cycle.
        for _ in 1..400_000 {
            for (i, t) in work.iter_mut().enumerate() {
                let left = i.checked_sub(1).map(|i| self.line[i]).unwrap_or(false);
                let right = *self.line.get(i + 1).unwrap_or(&false);
                *t = left != right;
            }
            std::mem::swap(&mut self.line, &mut work);
            count += self.line.iter().filter(|b| !**b).count();
        }
        count
    }
}
