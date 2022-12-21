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
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Expr {
    Num(String, isize),
    Add(String, String, String),
    Sub(String, String, String),
    Mul(String, String, String),
    Div(String, String, String),
    Var,
}

impl Expr {
    fn label(&self) -> &str {
        match self {
            Expr::Num(val, _) => val,
            Expr::Add(val, _, _) => val,
            Expr::Sub(val, _, _) => val,
            Expr::Mul(val, _, _) => val,
            Expr::Div(val, _, _) => val,
            Expr::Var            => "X",
        }
    }
    fn arg1(&self) -> &String {
        match self {
            Expr::Num(_, _) => unreachable!(),
            Expr::Add(_, val, _) => val,
            Expr::Sub(_, val, _) => val,
            Expr::Mul(_, val, _) => val,
            Expr::Div(_, val, _) => val,
            Expr::Var            => unreachable!(),
        }
    }
    fn arg2(&self) -> &String {
        match self {
            Expr::Num(_, _) => unreachable!(),
            Expr::Add(_, _, val) => val,
            Expr::Sub(_, _, val) => val,
            Expr::Mul(_, _, val) => val,
            Expr::Div(_, _, val) => val,
            Expr::Var            => unreachable!(),
        }
    }
    fn eval(&self, v1: isize, v2: isize) -> isize {
        match self {
            Expr::Num(_, _) => unreachable!(),
            Expr::Add(_, _, _) => v1 + v2,
            Expr::Sub(_, _, _) => v1 - v2,
            Expr::Mul(_, _, _) => v1 * v2,
            Expr::Div(_, _, _) => v1 / v2,
            Expr::Var            => unreachable!(),
        }
    }
    fn mnemonic(&self) -> &str {
        match self {
            Expr::Num(_, _) => unreachable!(),
            Expr::Add(_, _, _) => "+",
            Expr::Sub(_, _, _) => "-",
            Expr::Mul(_, _, _) => "*",
            Expr::Div(_, _, _) => "/",
            Expr::Var            => unreachable!(),
        }
    }
    fn build(&self, monkeys: &HashMap<String, Expr>, values: &HashMap<String, isize>) {
        match self {
            Expr::Num(n, val) if n == "humn" => print!("x"),
            Expr::Num(_, val) => print!("{val}"),
            Expr::Add(l, _, _) | Expr::Sub(l, _, _) | Expr::Mul(l, _, _) | Expr::Div(l, _, _) if values.contains_key(l)=> {
                print!("{}", values.get(l).unwrap());
                }
            Expr::Add(_, l, r) | Expr::Sub(_, l, r) | Expr::Mul(_, l, r) | Expr::Div(_, l, r) => {
                print!("(");
                let lm = monkeys.get(l).unwrap();
                lm.build(monkeys, values);
                print!("{}", self.mnemonic());
                let rm = monkeys.get(r).unwrap();
                rm.build(monkeys, values);
                print!(")");
            }
            Expr::Var => print!("X"),
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
                continue;
            };
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
                values.insert(m.label().to_string(), result);
            }
            std::mem::swap(&mut monkeys, &mut remain);
        }
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut values: HashMap<String, isize> = HashMap::new();
        let mut monkeys: Vec<&Expr> = Vec::new();
        for m in self.line.iter() {
            let Expr::Num(label, value) = m else { 
                if "root" != m.label() {
                    monkeys.push(m);
                }
                continue;
            };
            if "humn" != m.label() {
                values.insert(label.to_string(), *value);
            }
        }
        let mut generated = false;
        while generated {
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
                    continue;
                }
                values.insert(m.label().to_string(), result);
                generated = true;
            }
            std::mem::swap(&mut monkeys, &mut remain);
        }
        let mut generated = true;
        while generated {
            generated = false;
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
                values.insert(m.label().to_string(), result);
                generated = true;
            }
            std::mem::swap(&mut monkeys, &mut remain);
        }
        let mut monkeys: HashMap<String, Expr> = HashMap::new();
        for m in self.line.iter() {
            monkeys.insert(m.label().to_string(), m.clone());
        }
        let root = monkeys.get("root").unwrap();
        let left = root.arg1();
        let right = root.arg2();
        dbg!(left, right);
        let lm = monkeys.get(left).unwrap();
        lm.build(&monkeys, &values);
        println!();
        let rm = monkeys.get(right).unwrap();
        rm.build(&monkeys, &values);
        println!();
        let base = 3_757_272_361_000;
        for i in 0.. {
            let x = base + i;
            let d = 
 (10*(((131234706858508-((((((((924+((150+(((2*(((905+(((((((((((((2*((((3*(((((((854+(((37*((((((341+(((7*(187+((28+(((((((556+((((x-332)*36)+685)/5))*2)-737)+978)+164)/3)-16))/3)))-849)*2))+748)/7)-349)/4)+793))-61)/7))*8)-983)/7)+974)*2)-531))+181)/2)-548))+750)/2)-657)/11)+85)*28)+877)+709)/3)-430)*2)+839))/2)-60))-635)*2))/4))*2)-478)/2)-818)/3)+39)*7))/5)+553))
- 46779208742730;
            dbg!(d, x);
            if d <= 0 { 
                return x;
            }
        }
    unreachable!()
    }
}
