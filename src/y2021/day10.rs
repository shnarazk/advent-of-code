use crate::framework::{aoc_at, AdventOfCode, Maybe};

#[derive(Debug, PartialEq)]
pub struct Puzzle {
    line: Vec<String>,
}

#[aoc_at(2021, 10)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self { line: Vec::new() }
    }
    fn insert(&mut self, block: &str) -> Maybe<()> {
        self.line.push(block.trim().to_string());
        Ok(())
    }
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
                    _ => panic!(),
                };
            }
            dbg!(count);
            count
        }
        dbg!(&self.line);
        let mut v = self
            .line
            .iter()
            .map(|l| syntax_error(l))
            .filter(|v| 0 != *v)
            .collect::<Vec<_>>();

        v.sort_unstable();
        dbg!(&v);
        v[v.len() / 2]
    }
}
