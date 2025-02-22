//! <https://adventofcode.com/2020/day/10>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    vec: Vec<usize>,
}

#[aoc(2020, 10)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            self.vec.push(l.parse::<usize>()?);
        }
        self.vec.insert(0, 0);
        Self::parsed()
    }
    fn part1(&mut self) -> usize {
        self.vec.sort_unstable();
        let mut diff1 = 0;
        let mut diff3 = 0;
        for i in 1..self.vec.len() {
            match self.vec[i] - self.vec[i - 1] {
                1 => diff1 += 1,
                3 => diff3 += 1,
                _ => panic!("wrong"),
            }
        }
        diff3 += 1;
        assert_eq!(self.vec.len(), diff1 + diff3);
        diff1 * diff3
    }
    fn part2(&mut self) -> usize {
        self.vec.sort_unstable();
        let mx = *self.vec.last().unwrap();
        let mut count: Vec<usize> = vec![0; mx + 1];
        count[0] = 1;
        for n in &self.vec[1..] {
            count[*n] += count[*n - 1];
            if 2 <= *n {
                count[*n] += count[*n - 2];
            }
            if 3 <= *n {
                count[*n] += count[*n - 3];
            }
        }
        *count.last().unwrap()
    }
}
