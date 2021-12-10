#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::framework_ng::{AdventOfCode, Description, Maybe, ParseError};
use lazy_static::lazy_static;
use regex::Regex;
use std::collections::HashMap;

type DataSegment = String;

#[derive(Debug, PartialEq)]
struct Puzzle {
    line: Vec<String>,
}

impl AdventOfCode for Puzzle {
    type Segment = DataSegment;
    type Output1 = usize;
    type Output2 = usize;
    const YEAR: usize = 2021;
    const DAY: usize = 10;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self { line: Vec::new() }
    }
    // handle header
    // fn header(&mut self, input: &str) -> Maybe<Option<String>> {
    //     let parser: Regex = Regex::new(r"^(.+)\n\n((.|\n)+)$").expect("wrong");
    //     let segment = parser.captures(input).ok_or(ParseError)?;
    //     for num in segment[1].split(',') {
    //         let _value = num.parse::<usize>()?;
    //     }
    //     Ok(Some(segment[2].to_string()))
    // }
    /// add a data block
    fn insert(&mut self, block: &str) -> Maybe<()> {
        self.line.push(block.trim().to_string());
        Ok(())
    }
    // finalize
    // fn after_insert(&mut self) {}
    /// solver for part1
    fn part1(&mut self) -> usize {
        fn syntax_error(l: &str) -> usize {
            let mut stack: Vec<char> = Vec::new();
            for c in l.chars() {
                match c {
                    '(' | '[' | '{' | '<' => {
                        stack.push(c);
                    }
                    ')' => {
                        if stack.last() == Some(&'(') {
                            stack.pop();
                        } else {
                            return 3;
                        }
                    }
                    ']' => {
                        if stack.last() == Some(&'[') {
                            stack.pop();
                        } else {
                            return 57;
                        }
                    }
                    '}' => {
                        if stack.last() == Some(&'{') {
                            stack.pop();
                        } else {
                            return 1197;
                        }
                    }
                    '>' => {
                        if stack.last() == Some(&'<') {
                            stack.pop();
                        } else {
                            return 25137;
                        }
                    }
                    _ => panic!(),
                }
            }
            // assert!(stack.is_empty(), "{:?} => {:?}", l, &stack);
            0
        }
        dbg!(&self.line);
        self.line.iter().map(|l| syntax_error(l)).sum()
    }
    /// solver for part2
    fn part2(&mut self) -> usize {
        fn syntax_error(l: &str) -> usize {
            let mut stack: Vec<char> = Vec::new();
            for c in l.chars() {
                match c {
                    '(' | '[' | '{' | '<' => {
                        stack.push(c);
                    }
                    ')' => {
                        if stack.last() == Some(&'(') {
                            stack.pop();
                        } else {
                            return 0;
                        }
                    }
                    ']' => {
                        if stack.last() == Some(&'[') {
                            stack.pop();
                        } else {
                            return 0;
                        }
                    }
                    '}' => {
                        if stack.last() == Some(&'{') {
                            stack.pop();
                        } else {
                            return 0;
                        }
                    }
                    '>' => {
                        if stack.last() == Some(&'<') {
                            stack.pop();
                        } else {
                            return 0;
                        }
                    }
                    _ => panic!(),
                }
            }
            let mut count = 0;
            while let Some(ch) = stack.pop() {
                count *= 5;
                count += match ch {
                    '(' => 1,
                    '[' => 2,
                    '{' => 3,
                    '<' => 4,
                    _=> panic!(),
                };
            }
            dbg!(count);
            count
        }
        dbg!(&self.line);
        let mut v = self.line.iter().map(|l| syntax_error(l)).filter(|v| 0 != *v).collect::<Vec<_>>();
        
        v.sort();
        dbg!(&v);
        v[v.len() / 2]
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::solve(&desc, part));
}

#[cfg(test)]
mod test {
    use {
        super::*,
        crate::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        const TEST1: &str = "0\n1\n2";
        assert_eq!(
            Puzzle::parse(Description::TestData(TEST1.to_string()))
                .expect("-")
                .run(1),
            Answer::Part1(0)
        );
    }
}
