//! <https://adventofcode.com/2020/day/19>

use std::borrow::Borrow;

use {
    crate::framework::{aoc, AdventOfCode, Description, ParseError},
    lazy_static::lazy_static,
    regex::Regex,
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
    const DELIMITER: &'static str = "\n\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        lazy_static! {
            static ref R0: Regex = Regex::new(r#"^(\d+): "(.)""#).expect("error");
            static ref R1: Regex = Regex::new(r"^(\d+):(( \d+)+)$").expect("error");
            static ref R2: Regex = Regex::new(r"^(\d+):(( \d+)+) \|(( \d+)+)$").expect("error");
        }
        if let Some(m) = R0.captures(block) {
            let i = m[1].parse::<usize>().expect("wrong");
            let c = m[2].parse::<char>().expect("wrong");
            self.rule.insert(i, Rule::Match(c));
        } else if let Some(m) = R1.captures(block) {
            let i = m[1].parse::<usize>().expect("wrong");
            let mut vec: Vec<usize> = Vec::new();
            for n in m[2].split_ascii_whitespace() {
                vec.push(n.parse::<usize>().expect("strange"));
            }
            self.rule.insert(i, Rule::Seq(vec));
        } else if let Some(m) = R2.captures(block) {
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
    fn parse(desc: impl Borrow<Description>) -> Result<Self, ParseError> {
        let mut instance = Self::default();
        let buffer = Self::load(desc.borrow())?;
        let mut iter = buffer.split(Self::DELIMITER);
        if let Some(block) = iter.next() {
            for l in block.split('\n') {
                if !l.is_empty() {
                    instance.insert(l)?;
                }
            }
        }
        if let Some(block) = iter.next() {
            for line in block.split('\n') {
                if line.is_empty() {
                    break;
                }
                let cs = line.chars().collect::<Vec<char>>();
                instance.message.push(cs);
            }
        }
        Ok(instance)
    }
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

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        assert_eq!(
            Puzzle::solve(Description::FileTag("test1".to_string()), 1),
            Answer::Part1(2)
        );
    }

    #[test]
    fn test_part2() {
        assert_eq!(
            Puzzle::solve(Description::FileTag("test2".to_string()), 2),
            Answer::Part2(12)
        );
    }
}
