//! <https://adventofcode.com/2016/day/21>
use crate::framework::{AdventOfCode, ParseError, aoc_at};
use std::collections::VecDeque;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum OpCode {
    Swap0(usize, usize),
    Swap1(u8, u8),
    Reverse(usize, usize),
    Rotate0(bool, usize),
    Move(usize, usize),
    Rotate1(u8),
}
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<OpCode>,
}

mod parser {
    use {
        super::*,
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, opt, separated, seq},
            token::one_of,
        },
    };

    fn parse_opcode(s: &mut &str) -> ModalResult<OpCode> {
        alt((
            seq!(_: "swap position ", parse_usize, _: " with position ", parse_usize)
                .map(|(a, b)| OpCode::Swap0(a, b)),
            seq!(_: "swap letter ", one_of(|c: char| c.is_ascii_lowercase()), _: " with letter ", one_of(|c: char| c.is_ascii_lowercase())).map(|(a, b)| OpCode::Swap1(a as u8, b as u8)),
            seq!(_: "reverse positions ", parse_usize, _: " through ", parse_usize).map(|(a, b)| OpCode::Reverse(a, b)),
            seq!(_: "rotate left ", parse_usize, _: (" step", opt('s'))).map(|(n,)| OpCode::Rotate0(false, n)),
            seq!(_: "rotate right ", parse_usize, _: (" step", opt('s'))).map(|(n,)| OpCode::Rotate0(true, n)),
            seq!(_: "move position ", parse_usize, _: " to position ", parse_usize).map(|(a, b)| OpCode::Move(a, b)),
            seq!(_: "rotate based on position of letter ", one_of(|c: char| c.is_ascii_lowercase())).map(|(c,):( char,)| OpCode::Rotate1(c as u8)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<OpCode>> {
        separated(1.., parse_opcode, newline).parse_next(s)
    }
}

#[aoc_at(2016, 21)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = String;
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut phrase: VecDeque<u8> = VecDeque::from(b"abcdefgh".to_vec());
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
        }
        phrase.iter().map(|c| *c as char).collect::<String>()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut phrase: VecDeque<u8> = VecDeque::from(b"fbgdceah".to_vec());
        for code in self.line.iter().rev() {
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
                    if !*to_right {
                        phrase.rotate_right(*arg);
                    } else {
                        phrase.rotate_left(*arg);
                    }
                }
                OpCode::Move(arg2, arg1) => {
                    let c = phrase.remove(*arg1).unwrap();
                    phrase.insert(*arg2, c);
                }
                OpCode::Rotate1(arg) => {
                    for (j, c) in phrase.iter().enumerate() {
                        if *c == *arg {
                            let m = phrase.len();
                            let i = match j {
                                1 => 0,
                                3 => 1,
                                5 => 2,
                                7 => 3,
                                2 => 4,
                                4 => 5,
                                6 => 6,
                                0 => 7,
                                _ => unreachable!(),
                            };
                            phrase.rotate_left((m + j - i) % m);
                            break;
                        }
                    }
                }
            }
        }
        phrase.iter().map(|c| *c as char).collect::<String>()
    }
}
