//! <https://adventofcode.com/2015/day/18>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser,
    },
    lazy_static::lazy_static,
    regex::Regex,
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<()>,
}

#[aoc(2015, 18)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    // fn header(&mut self, input: String) -> Result<Option<String>, ParseError> {
    //     let parser: Regex = Regex::new(r"^(.+)\n\n((.|\n)+)$").expect("wrong");
    //     let segment = parser.captures(input).ok_or(ParseError)?;
    //     for num in segment[1].split(',') {
    //         let _value = num.parse::<usize>()?;
    //     }
    //     Ok(Some(segment[2].to_string()))
    // }
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        lazy_static! {
            static ref PARSER: Regex = Regex::new(r"^([0-9]+)$").expect("wrong");
        }
        let segment = PARSER.captures(block).ok_or(ParseError)?;
        // self.line.push(segment[1].parse::<_>());
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

#[cfg(feature = "y2015")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        assert_eq!(
            Puzzle::solve(Description::TestData("".to_string()), 1),
            Answer::Part1(0)
        );
    }
}
