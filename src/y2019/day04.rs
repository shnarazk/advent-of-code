//! <https://adventofcode.com/2019/day/4>
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

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<usize>,
}

#[aoc(2019, 4)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        if let Ok(v) = line_parser::to_usizes(block, '-') {
            self.line = v;
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut count = 0;
        for i in self.line[0]..=self.line[1] {
            let s = format!("{i}").chars().map(|c| c as u8).collect::<Vec<u8>>();
            if s.windows(2).any(|v| v[0] == v[1]) && s.windows(2).all(|v| v[0] <= v[1]) {
                count += 1;
            }
        }
        count
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
