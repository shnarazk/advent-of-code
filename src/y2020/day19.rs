//! <https://adventofcode.com/2020/day/19>

use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashMap,
};

#[derive(Clone, Debug, PartialEq)]
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

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    rule: HashMap<usize, Rule>,
    message: Vec<Vec<char>>,
}

mod parser {
    use {
        super::Rule,
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, repeat, separated, seq},
            token::one_of,
        },
    };

    fn parse_rule(s: &mut &str) -> ModalResult<(usize, Rule)> {
        alt((
            seq!(
                parse_usize,
                _: ": \"",
                one_of('a'..='z'),
                _: "\"\n"
            )
            .map(|(n, c)| (n, Rule::Match(c))),
            seq!(
                parse_usize,
                _: ": ",
                separated(1.., parse_usize, " "),
                _: newline,
            )
            .map(|(n, v)| (n, Rule::Seq(v))),
            seq!(
                parse_usize,
                _: ": ",
                separated(1.., parse_usize, " "),
                _: " | ",
                separated(1.., parse_usize, " "),
                _: newline,
            )
            .map(|(n, va, vb)| (n, Rule::Or(va, vb))),
        ))
        .parse_next(s)
    }

    pub fn parse_message(s: &mut &str) -> ModalResult<Vec<char>> {
        repeat(1.., alt(('a', 'b'))).parse_next(s)
    }
    #[allow(clippy::type_complexity)]
    pub fn parse(s: &mut &str) -> ModalResult<(Vec<(usize, Rule)>, Vec<Vec<char>>)> {
        seq!(
            repeat(1.., parse_rule),
            _: newline,
            separated(1.., parse_message, newline)
        )
        .parse_next(s)
    }
}

#[aoc(2020, 19)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        let (rules, messages) = parser::parse(&mut input)?;
        let r = rules.iter().cloned().collect::<HashMap<usize, Rule>>();
        self.rule = r;
        self.message = messages;
        Ok(())
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
