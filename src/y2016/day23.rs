//! <https://adventofcode.com/2016/day/23>
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

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Reg {
    R(char),
    Lit(isize),
}

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Code {
    Cpy(Reg, Reg),
    Inc(Reg),
    Dec(Reg),
    Jnp(isize, Reg),
    Tgl(Reg),
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Code>,
}

#[aoc(2016, 23)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^([0-9]+)$");
        if let Ok(segment) = parser.captures(block).ok_or(ParseError) {}
        // self.line.push(segment[0].parse::<_>());
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

#[cfg(feature = "y2016")]
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
