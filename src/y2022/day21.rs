//! <https://adventofcode.com/2022/day/21>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};
#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Expr {
    Num(String, isize),
    Add(String, String, String),
    Sub(String, String, String),
    Mul(String, String, String),
    Div(String, String, String),
}

impl Expr {
    fn label(&self) -> &String {
        match self {
            Expr::Num(_, _) => unreachable!(),
            Expr::Add(val, _, _) => val,
            Expr::Sub(val, _, _) => val,
            Expr::Mul(val, _, _) => val,
            Expr::Div(val, _, _) => val,
        }
    }
    fn arg1(&self) -> &String {
        match self {
            Expr::Num(_, _) => unreachable!(),
            Expr::Add(_, val, _) => val,
            Expr::Sub(_, val, _) => val,
            Expr::Mul(_, val, _) => val,
            Expr::Div(_, val, _) => val,
        }
    }
    fn arg2(&self) -> &String {
        match self {
            Expr::Num(_, _) => unreachable!(),
            Expr::Add(_, _, val) => val,
            Expr::Sub(_, _, val) => val,
            Expr::Mul(_, _, val) => val,
            Expr::Div(_, _, val) => val,
        }
    }
    fn eval(&self, v1: isize, v2: isize) -> isize {
        match self {
            Expr::Num(_, _) => unreachable!(),
            Expr::Add(_, _, _) => v1 + v2,
            Expr::Sub(_, _, _) => v1 - v2,
            Expr::Mul(_, _, _) => v1 * v2,
            Expr::Div(_, _, _) => v1 / v2,
        }
    }
}

#[derive(Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Expr>,
}

#[aoc_at(2022, 21)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let num_parser = regex!(r"^(\w{4}): (\d+)$");
        let term_parser = regex!(r"^(\w{4}): (\w{4}) (\+|-|\*|/) (\w{4})$");
        if let Some(segment) = num_parser.captures(block) {
            let dest = segment[1].to_string();
            let num = segment[2].parse::<isize>()?;
            self.line.push(Expr::Num(dest, num));
        } else if let Some(segment) = term_parser.captures(block) {
            let dest = segment[1].to_string();
            let src1 = segment[2].to_string();
            let src2 = segment[4].to_string();
            self.line.push(match &segment[3] {
                "+" => Expr::Add(dest, src1, src2),
                "-" => Expr::Sub(dest, src1, src2),
                "*" => Expr::Mul(dest, src1, src2),
                "/" => Expr::Div(dest, src1, src2),
                _ => unreachable!(),
            });
        } else {
            dbg!(block);
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut values: HashMap<String, isize> = HashMap::new();
        let mut monkeys: Vec<&Expr> = Vec::new();
        for m in self.line.iter() {
            let Expr::Num(label, value) = m else { 
                monkeys.push(m);
                continue;};
            values.insert(label.to_string(), *value);
        }
        loop {
            let mut remain = Vec::new();
            while let Some(m) = monkeys.pop() {
                let a1 = m.arg1();
                let a2 = m.arg2();
                let Some(v1) = values.get(a1) else {
                    remain.push(m);       
                    continue;
                };
                let Some(v2) = values.get(a2) else {
                    remain.push(m);       
                    continue;
                };
                let result = m.eval(*v1, *v2);
                if m.label() == "root" {
                    return result;
                }
                values.insert(m.label().clone(), result);
            }
            std::mem::swap(&mut monkeys, &mut remain);
        }
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
