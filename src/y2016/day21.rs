//! <https://adventofcode.com/2016/day/21>
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
enum OpCode {
    Swap0(usize, usize),
    Swap1(char, char),
    Reverse(usize, usize),
    Rotate0(isize),
    Move(usize, usize),
    Rotate1(char),
}
#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<OpCode>,
}

#[aoc(2016, 21)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let rule0 = regex!(r"swap position (\d+) with position (\d+)");
        let rule1 = regex!(r"swap letter ([[:alpha:]]) with letter ([[:alpha:]])");
        let rule2 = regex!(r"reverse positions (\d+) through (\d+)");
        let rule3 = regex!(r"rotate (left|right) (\d+) step");
        let rule4 = regex!(r"move position (\d+) to position (\d+)");
        let rule5 = regex!(r"rotate based on position of letter ([[:alpha:]])");
        if let Some(segment) = rule0.captures(block) {
            let arg1 = line_parser::to_usize(&segment[1])?;
            let arg2 = line_parser::to_usize(&segment[2])?;
            self.line.push(OpCode::Swap0(arg1, arg2));
        }
        if let Some(segment) = rule1.captures(block) {
            let arg1 = segment[1].chars().next().unwrap();
            let arg2 = segment[2].chars().next().unwrap();
            self.line.push(OpCode::Swap1(arg1, arg2));
        }
        if let Some(segment) = rule2.captures(block) {
            let arg1 = line_parser::to_usize(&segment[1])?;
            let arg2 = line_parser::to_usize(&segment[2])?;
            self.line.push(OpCode::Reverse(arg1, arg2));
        }
        if let Some(segment) = rule3.captures(block) {
            let arg1 = line_parser::to_isize(&segment[1])?;
            let arg = if segment[1] == *"left" { arg1 } else { -arg1 };
            self.line.push(OpCode::Rotate0(arg));
        }
        if let Some(segment) = rule4.captures(block) {
            let arg1 = line_parser::to_usize(&segment[1])?;
            let arg2 = line_parser::to_usize(&segment[2])?;
            self.line.push(OpCode::Move(arg1, arg2));
        }
        if let Some(segment) = rule5.captures(block) {
            let arg1 = segment[1].chars().next().unwrap();
            self.line.push(OpCode::Rotate1(arg1));
        }
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
