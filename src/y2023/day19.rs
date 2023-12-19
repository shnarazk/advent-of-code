//! <https://adventofcode.com/2023/day/19>
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

type Label = String;
type Var = String;
type Val = isize;
#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Op {
    Less,
    Greater,
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    rules: HashMap<Label, Vec<(Var, Op, Val, Label)>>,
    settings: Vec<HashMap<Var, Val>>,
    reading_settings: bool,
}

impl Puzzle {
    fn execute(&self, label: &Label) -> bool {
        let Some(rules) = self.rules.get(label) else {
            panic!();
        };
        rules
            .iter()
            .any(|(var, op, val, label)| match op {_ => false } && self.execute(label))
    }
    fn check(&self) -> bool {
        self.execute(&"in".to_string())
    }
}

#[aoc(2023, 19)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        dbg!(block);
        let rule_parser = regex!(r"^([A-Za-z]+)\{(.+)\}$");
        let assign_parser = regex!(r"^\{(.+)\}$");
        if let Some(segment) = rule_parser.captures(block) {
            let name = segment[1].to_string();
            for pat in segment[2].split(',') {
                let conds_and_label = pat.split(':').collect::<Vec<_>>();
                for i in 0..conds_and_label.len() - 1 {
                    let parser2 = regex!(r"^([A-Za-z]+)(>|<)(\d+)$");
                    dbg!(conds_and_label[0]);
                    let cov = parser2.captures(conds_and_label[0]).ok_or(ParseError)?;
                    dbg!(&cov[2]);
                    dbg!(conds_and_label[i]);
                }
                let label = dbg!(conds_and_label.last().unwrap());
            }
        } else if let Some(segment) = assign_parser.captures(block) {
        } else {
            panic!();
        }
        Ok(())
    }
    fn end_of_data(&mut self) {
        dbg!(&self.rules);
    }
    fn part1(&mut self) -> Self::Output1 {
        1
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
