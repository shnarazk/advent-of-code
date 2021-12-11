use crate::framework::{AdventOfCode, Description, Maybe};

#[derive(Debug, PartialEq)]
struct Puzzle {
    line: Vec<String>,
}

impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = usize;
    const YEAR: usize = 2021;
    const DAY: usize = 10;
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

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::solve(&desc, part));
}
