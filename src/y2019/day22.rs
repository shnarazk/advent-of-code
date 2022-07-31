//! <https://adventofcode.com/2019/day/22>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Eq, Hash, PartialEq)]
enum Shuffle {
    Stack,
    Cut(i32),
    Increment(u32),
}

impl Shuffle {
    fn cancel(&self, n: usize) -> usize {
        0
    }
}

#[derive(Debug, Default, Eq, Hash, PartialEq)]
pub struct Puzzle {
    line: Vec<Shuffle>,
}

#[aoc(2019, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let stack = regex!(r"^deal into new stack$");
        let cut = regex!(r"^cut (-?\d+)$");
        let increment = regex!(r"^deal with increment (\d+)$");
        if let Some(segment) = stack.captures(block) {
            self.line.push(Shuffle::Stack);
        } else if let Some(segment) = cut.captures(block) {
            let val: i32 = segment[1].parse::<i32>()?;
            self.line.push(Shuffle::Cut(val));
        } else if let Some(segment) = increment.captures(block) {
            let val: u32 = segment[1].parse::<u32>()?;
            self.line.push(Shuffle::Increment(val));
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut index: usize = 10;
        while let Some(shuffle) = self.line.pop() {
            index = shuffle.cancel(index);
        }
        index
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

#[cfg(feature = "y2019")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    // #[test]
    // fn test_part1() {
    //     assert_eq!(
    //         Puzzle::solve(Description::TestData("".to_string()), 1),
    //         Answer::Part1(0)
    //     );
    // }
}
