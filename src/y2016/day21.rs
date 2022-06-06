//! <https://adventofcode.com/2016/day/21>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::collections::VecDeque;
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
    Swap1(u8, u8),
    Reverse(usize, usize),
    Rotate0(bool, usize),
    Move(usize, usize),
    Rotate1(u8),
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
        let rule3 = regex!(r"rotate (left|right) (\d+) steps?");
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
            self.line.push(OpCode::Swap1(arg1 as u8, arg2 as u8));
        }
        if let Some(segment) = rule2.captures(block) {
            let arg1 = line_parser::to_usize(&segment[1])?;
            let arg2 = line_parser::to_usize(&segment[2])?;
            self.line.push(OpCode::Reverse(arg1, arg2));
        }
        if let Some(segment) = rule3.captures(block) {
            let arg = line_parser::to_usize(&segment[2])?;
            self.line.push(OpCode::Rotate0(segment[1] == *"right", arg));
        }
        if let Some(segment) = rule4.captures(block) {
            let arg1 = line_parser::to_usize(&segment[1])?;
            let arg2 = line_parser::to_usize(&segment[2])?;
            self.line.push(OpCode::Move(arg1, arg2));
        }
        if let Some(segment) = rule5.captures(block) {
            let arg1 = segment[1].chars().next().unwrap();
            self.line.push(OpCode::Rotate1(arg1 as u8));
        }
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        // let mut phrase: VecDeque<u8> = VecDeque::from(b"abcdefgh".to_vec());
        let mut phrase: VecDeque<u8> = VecDeque::from(b"abcde".to_vec());
        for code in self.line.iter() {
            match code {
                OpCode::Swap0(arg1, arg2) => {
                    phrase.swap(*arg1, *arg2);
                }
                OpCode::Swap1(arg1, arg2) => {
                    for c in phrase.iter_mut() {
                        match *c {
                            _ if *c == *arg1 => *c = *arg2,
                            _ if *c == *arg2 => *c = *arg1,
                            _ => (),
                        }
                    }
                }
                OpCode::Reverse(arg1, arg2) => {
                    let mut left = *arg1;
                    let mut right = *arg2;
                    while left < right {
                        phrase.swap(left, right);
                        left += 1;
                        right -= 1;
                    }
                }
                OpCode::Rotate0(to_right, arg) => {
                    if *to_right {
                        phrase.rotate_right(*arg);
                    } else {
                        phrase.rotate_left(*arg);
                    }
                }
                OpCode::Move(arg1, arg2) => {
                    let c = phrase.remove(*arg1).unwrap();
                    phrase.insert(*arg2, c);
                }
                OpCode::Rotate1(arg) => {
                    for (i, c) in phrase.iter().enumerate() {
                        if *c == *arg {
                            let r = 1 + i + ((4 <= i) as usize);
                            phrase.rotate_right(r % phrase.len());
                            break;
                        }
                    }
                }
            }
            dbg!(String::from_utf8_lossy(
                &phrase.iter().copied().collect::<Vec<u8>>()
            ));
        }
        dbg!(String::from_utf8_lossy(
            &phrase.iter().copied().collect::<Vec<u8>>()
        ));
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
