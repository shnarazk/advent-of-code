//! <https://adventofcode.com/2020/day/15>
#![allow(unused_imports)]
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    dic: HashMap<usize, usize>,
    last: usize,
    clock: usize,
}

#[aoc(2020, 15)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = ",";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        if let Ok(n) = block.trim().parse::<usize>() {
            self.clock += 1;
            *self.dic.entry(n).or_insert(0) = self.clock;
            self.last = n;
        }
        Ok(())
    }
    fn part1(&mut self) -> usize {
        self.run_to(2020)
    }
    fn part2(&mut self) -> usize {
        self.run_to(30000000)
    }
}

impl Puzzle {
    fn run_to(&mut self, limit: usize) -> usize {
        self.clock += 1;
        loop {
            let last_entry = self.dic.entry(self.last).or_insert(0);
            if *last_entry == 0 {
                *last_entry = self.clock - 1;
                self.last = 0;
            } else {
                self.last = self.clock - 1 - *last_entry;
                *last_entry = self.clock - 1;
            }
            if limit == self.clock {
                return self.last;
            }
            self.clock += 1;
        }
    }
}

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        assert_eq!(
            Puzzle::solve(Description::TestData("1,3,2".to_string()), 1),
            Answer::Part1(1)
        );
        assert_eq!(
            Puzzle::solve(Description::TestData("2,1,3".to_string()), 1),
            Answer::Part1(10)
        );
        assert_eq!(
            Puzzle::solve(Description::TestData("1,2,3".to_string()), 1),
            Answer::Part1(27)
        );
        assert_eq!(
            Puzzle::solve(Description::TestData("2,3,1".to_string()), 1),
            Answer::Part1(78)
        );
        assert_eq!(
            Puzzle::solve(Description::TestData("3,2,1".to_string()), 1),
            Answer::Part1(438)
        );
        assert_eq!(
            Puzzle::solve(Description::TestData("3,1,2".to_string()), 1),
            Answer::Part1(1836)
        );
    }
    #[test]
    fn test_part2() {
        assert_eq!(
            Puzzle::solve(Description::TestData("0,3,6".to_string()), 2),
            Answer::Part2(175594)
        );
        assert_eq!(
            Puzzle::solve(Description::TestData("1,3,2".to_string()), 2),
            Answer::Part2(2578)
        );
    }
}
