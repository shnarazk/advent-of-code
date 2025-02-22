//! <https://adventofcode.com/2016/day/19>
use crate::{
    framework::{AdventOfCode, ParseError, aoc},
    parser,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    input: usize,
}

#[aoc(2016, 19)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, s: &str) -> Result<(), ParseError> {
        for l in s.lines() {
            self.input = parser::to_usize(l)?;
        }
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        // self.input = 5;
        let mut next = vec![0];
        for i in 1..=self.input {
            next.push(i + 1);
        }
        next[self.input] = 1;
        let mut index = 1;
        while next[index] != index {
            let i = next[next[index]];
            next[index] = i;
            index = i;
        }
        index
    }
    fn part2(&mut self) -> Self::Output2 {
        // self.input = 5;
        let mut next = vec![0];
        for i in 1..=self.input {
            next.push(i + 1);
        }
        next[self.input] = 1;
        let mut remain = self.input;
        let mut index = self.input / 2;
        let mut dist = index;
        while next[index] != index {
            let i = next[next[index]];
            // println!("remain: {remain}, dist: {dist}, {index} directs to {i}");
            next[index] = i;
            remain -= 1;
            if dist == remain / 2 {
                index = i;
            } else {
                dist -= 1;
            }
            debug_assert_eq!(remain / 2, dist);
        }
        index
    }
}
