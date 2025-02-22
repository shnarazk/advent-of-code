//! <https://adventofcode.com/2017/day/9>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: String,
}

#[aoc(2017, 9)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input.to_string();
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut total = 0;
        let mut level = 0;
        let mut in_garbage = false;
        let mut after_bang = false;
        for ch in self.line.chars() {
            match ch {
                _ if after_bang => {
                    after_bang = false;
                }
                '{' if !in_garbage => {
                    level += 1;
                    total += level;
                }
                '}' if !in_garbage => {
                    level -= 1;
                }
                '<' if !in_garbage => {
                    in_garbage = true;
                }
                '>' => {
                    in_garbage = false;
                }
                '!' if in_garbage => {
                    after_bang = true;
                }
                _ => {}
            }
        }
        total
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut total = 0;
        let mut in_garbage = false;
        let mut after_bang = false;
        for ch in self.line.chars() {
            match ch {
                _ if after_bang => {
                    after_bang = false;
                }
                '{' | '}' if !in_garbage => {}
                '<' if !in_garbage => {
                    in_garbage = true;
                }
                '>' => {
                    in_garbage = false;
                }
                '!' if in_garbage => {
                    after_bang = true;
                }
                _ => {
                    if in_garbage {
                        total += 1;
                    }
                }
            }
        }
        total
    }
}
