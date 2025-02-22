//! <https://adventofcode.com/2015/day/24>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        progress,
    },
    std::{cmp::Reverse, collections::BinaryHeap},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<usize>,
}
type Cand = (usize, usize, [bool; 29], usize);

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{ModalResult, Parser, ascii::newline, combinator::separated},
    };

    pub fn parse(s: &mut &str) -> ModalResult<Vec<usize>> {
        separated(1.., parse_usize, newline).parse_next(s)
    }
}
#[aoc(2015, 24)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut block: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut block)?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.reverse();
        let noptions = self.line.len();
        let mut test = 0;
        let target: usize = self.line.iter().sum::<usize>() / 3;
        let mut to_visit: BinaryHeap<Reverse<Cand>> = BinaryHeap::new();
        to_visit.push(Reverse((0, 1, [false; 29], 0)));
        while let Some(Reverse(smallest)) = to_visit.pop() {
            let len = smallest.0;
            let qe = smallest.1;
            let sum = smallest
                .2
                .iter()
                .enumerate()
                .filter(|(_, b)| **b)
                .map(|(i, _)| self.line[i])
                .sum::<usize>();
            if sum == target {
                return qe;
            }
            if target < sum {
                continue;
            }
            if test < sum {
                progress!(format!("{}/{} (QE={})", sum, len, qe));
                test = sum;
            }
            for k in smallest.3..noptions {
                if smallest.2[k] || target < sum + self.line[k] {
                    continue;
                }
                let mut new = smallest;
                new.0 += 1;
                new.1 *= self.line[k];
                new.2[k] = true;
                new.3 = k + 1;
                to_visit.push(Reverse(new));
            }
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line.reverse();
        let noptions = self.line.len();
        let mut test = 0;
        let target: usize = self.line.iter().sum::<usize>() / 4;
        let mut to_visit: BinaryHeap<Reverse<Cand>> = BinaryHeap::new();
        to_visit.push(Reverse((0, 1, [false; 29], 0)));
        while let Some(Reverse(smallest)) = to_visit.pop() {
            let len = smallest.0;
            let qe = smallest.1;
            let sum = smallest
                .2
                .iter()
                .enumerate()
                .filter(|(_, b)| **b)
                .map(|(i, _)| self.line[i])
                .sum::<usize>();
            if sum == target {
                return qe;
            }
            if target < sum {
                continue;
            }
            if test < sum {
                progress!(format!("{}/{} (QE={})", sum, len, qe));
                test = sum;
            }
            for k in smallest.3..noptions {
                if smallest.2[k] || target < sum + self.line[k] {
                    continue;
                }
                let mut new = smallest;
                new.0 += 1;
                new.1 *= self.line[k];
                new.2[k] = true;
                new.3 = k + 1;
                to_visit.push(Reverse(new));
            }
        }
        0
    }
}
