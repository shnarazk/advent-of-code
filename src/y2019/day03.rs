//! <https://adventofcode.com/2019/day/3>
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
    line: Vec<Vec<(isize, isize)>>,
}

#[aoc(2019, 3)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        dbg!(&block);
        let parser = regex!(r"^([URDL])(\d+)");
        let mut vec = Vec::new();
        for segment in block.split(',') {
            if let Some(seg) = parser.captures(segment) {
                match (&seg[1], seg[2].parse::<isize>()) {
                    ("U", Ok(d)) => vec.push((-d, 0)),
                    ("D", Ok(d)) => vec.push((d, 0)),
                    ("L", Ok(d)) => vec.push((0, -d)),
                    ("R", Ok(d)) => vec.push((0, d)),
                    _ => panic!(),
                }
            }
        }
        self.line.push(vec);
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        0
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
