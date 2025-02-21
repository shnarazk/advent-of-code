//! <https://adventofcode.com/2021/day/10>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<String>,
}

#[aoc(2021, 10)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input.lines().map(|l| l.to_string()).collect();
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
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
        self.line.iter().map(|l| syntax_error(l)).sum()
    }
    fn part2(&mut self) -> Self::Output2 {
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
                    _ => panic!(),
                };
            }
            count
        }
        let mut v = self
            .line
            .iter()
            .map(|l| syntax_error(l))
            .filter(|v| 0 != *v)
            .collect::<Vec<_>>();

        v.sort_unstable();
        v[v.len() / 2]
    }
}
