//! <https://adventofcode.com/2020/day/19>

use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, PartialEq)]
enum Rule {
    Match(char),
    Or(Vec<usize>, Vec<usize>),
    Seq(Vec<usize>),
}

// #[derive(Debug, Default, PartialEq)]
// struct NumberedRule {
//     num: usize,
//     rule: Rule,
// }

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    rule: HashMap<usize, Rule>,
    message: Vec<Vec<char>>,
}

#[aoc(2020, 19)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let r0 = regex!(r#"^(\d+): "(.)""#);
        let r1 = regex!(r"^(\d+):(( \d+)+)$");
        let r2 = regex!(r"^(\d+):(( \d+)+) \|(( \d+)+)$");
        if let Some(m) = r0.captures(block) {
            let i = m[1].parse::<usize>().expect("wrong");
            let c = m[2].parse::<char>().expect("wrong");
            self.rule.insert(i, Rule::Match(c));
        } else if let Some(m) = r1.captures(block) {
            let i = m[1].parse::<usize>().expect("wrong");
            let mut vec: Vec<usize> = Vec::new();
            for n in m[2].split_ascii_whitespace() {
                vec.push(n.parse::<usize>().expect("strange"));
            }
            self.rule.insert(i, Rule::Seq(vec));
        } else if let Some(m) = r2.captures(block) {
            let i = m[1].parse::<usize>().expect("wrong");
            let mut vec1: Vec<usize> = Vec::new();
            for n in m[2].split_ascii_whitespace() {
                vec1.push(n.parse::<usize>().expect("strange"));
            }
            let mut vec2: Vec<usize> = Vec::new();
            for n in m[4].split_ascii_whitespace() {
                vec2.push(n.parse::<usize>().expect("strange"));
            }
            self.rule.insert(i, Rule::Or(vec1, vec2));
        }
        Ok(())
    }
    fn parse(&mut self, buffer: String) -> Result<String, ParseError> {
        let mut iter = buffer.split("\n\n");
        let rules = iter.next().unwrap();
        if let Some(block) = iter.next() {
            for line in block.split('\n') {
                if line.is_empty() {
                    break;
                }
                let cs = line.chars().collect::<Vec<char>>();
                self.message.push(cs);
            }
        }
        Ok(rules.to_string())
    }
    fn end_of_data(&mut self) {}
    fn part1(&mut self) -> usize {
        self.message
            .iter()
            .filter(|m| check_trace(&self.rule, &mut vec![0], m, 0))
            .count()
    }
    fn part2(&mut self) -> usize {
        self.rule.insert(8, Rule::Or(vec![42], vec![42, 8]));
        self.rule
            .insert(11, Rule::Or(vec![42, 31], vec![42, 11, 31]));

        self.message
            .iter()
            .filter(|m| check_trace(&self.rule, &mut vec![0], m, 0))
            .count()
    }
}

fn check_trace(
    rule: &HashMap<usize, Rule>,
    stack: &mut Vec<usize>,
    target: &[char],
    from: usize,
) -> bool {
    if let Some(index) = stack.pop() {
        if !stack.is_empty() && target.len() <= from {
            return false;
        }
        if let Some(r) = rule.get(&index) {
            match r {
                Rule::Match(c) => {
                    // println!(
                    //     "try match: {} against {}",
                    //     index,
                    //     target[from..].iter().collect::<String>()
                    // );
                    if target[from] != *c {
                        return false;
                    }
                    return check_trace(rule, stack, target, from + 1);
                }
                Rule::Seq(vec) => {
                    // println!(
                    //     "try seq: {} against {}",
                    //     index,
                    //     target[from..].iter().collect::<String>()
                    // );
                    for i in vec.iter().rev() {
                        stack.push(*i);
                    }
                    return check_trace(rule, stack, target, from);
                }
                Rule::Or(vec1, vec2) => {
                    let mut stack2 = stack.clone();
                    for i in vec1.iter().rev() {
                        stack.push(*i);
                    }
                    let try1 = check_trace(rule, stack, target, from);
                    if try1 {
                        return true;
                    }
                    for i in vec2.iter().rev() {
                        stack2.push(*i);
                    }
                    // println!("backtrack of rule {}: {:?}", index, vec2);
                    return check_trace(rule, &mut stack2, target, from);
                }
            }
        } else {
            panic!(
                "here stack.{}, from.{}, len.{}",
                stack.len(),
                from,
                target.len()
            );
            // return target.len() == from;
        }
    }
    target.len() == from
}
