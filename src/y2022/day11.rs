//! <https://adventofcode.com/2022/day/11>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    line_parser, regex,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Monkey {
    id: usize,
    items: Vec<usize>,
    operation: (bool, Option<usize>),
    test: usize,
    test_then: usize,
    test_else: usize,
    num_inspect: usize,
}

impl Monkey {
    fn update(&mut self, thrown: &mut [Vec<usize>]) {
        for i in self.items.iter() {
            self.num_inspect += 1;
            let mut j = match self.operation {
                (false, None) => i + i,
                (false, Some(k)) => i + k,
                (true, None) => i * i,
                (true, Some(k)) => i * k,
            };
            j /= 3;
            thrown[if j % self.test == 0 {
                self.test_then
            } else {
                self.test_else
            }]
            .push(j);
        }
        self.items.clear();
    }
    fn update2(&mut self, thrown: &mut [Vec<usize>], cd: usize) {
        for i in self.items.iter() {
            self.num_inspect += 1;
            let j = match self.operation {
                (false, None) => i + i,
                (false, Some(k)) => i + k,
                (true, None) => i * i,
                (true, Some(k)) => i * k,
            };
            thrown[if j % self.test == 0 {
                self.test_then
            } else {
                self.test_else
            }]
            .push(j % cd);
        }
        self.items.clear();
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Monkey>,
}

#[aoc(2022, 11)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(
            r"^Monkey (\d+):\n  Starting items: (.+)\n  Operation: new = old (.) (.+)\n  Test: divisible by (.+)\n    If true: throw to monkey (\d+)\n    If false: throw to monkey (\d+)\n?$"
        );
        if let Some(segment) = parser.captures(block) {
            self.line.push(Monkey {
                id: segment[1].parse::<usize>()?,
                items: line_parser::to_usizes(&segment[2], '\t')?,
                operation: (&segment[3] == "*", segment[4].parse::<usize>().ok()),
                test: segment[5].parse::<usize>()?,
                test_then: segment[6].parse::<usize>()?,
                test_else: segment[7].parse::<usize>()?,
                ..Default::default()
            });
        }
        Ok(())
    }
    fn wrap_up(&mut self) {
        // dbg!(&self.line.len());
    }
    fn dump(&self) {
        for m in self.line.iter() {
            println!(
                "{},{},{},{},{},{},{}",
                m.id,
                m.operation.0 as usize,
                m.operation.1.unwrap_or(0),
                m.test,
                m.test_then,
                m.test_else,
                m.items
                    .iter()
                    .map(|i| format!("{i}"))
                    .collect::<Vec<_>>()
                    .join(","),
            );
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut tmp = vec![Vec::new(); self.line.len()];
        for _ in 0..20 {
            for i in 0..self.line.len() {
                let m = &mut self.line[i];
                m.update(&mut tmp);
                self.thrown(&mut tmp);
            }
            println!(
                "{:?}",
                self.line.iter().map(|m| &m.items).collect::<Vec<_>>()
            );
        }
        dbg!(self
            .line
            .iter()
            .map(|m| m.num_inspect)
            .collect::<Vec<usize>>());
        let mut v = self
            .line
            .iter()
            .map(|m| m.num_inspect)
            .collect::<Vec<usize>>();
        v.sort();
        v.reverse();
        v[0] * v[1]
    }
    fn part2(&mut self) -> Self::Output2 {
        let cd = self.line.iter().map(|m| m.test).product();
        let mut tmp = vec![Vec::new(); self.line.len()];
        for _ in 0..10000 {
            for i in 0..self.line.len() {
                let m = &mut self.line[i];
                m.update2(&mut tmp, cd);
                self.thrown(&mut tmp);
            }
        }
        dbg!(self
            .line
            .iter()
            .map(|m| m.num_inspect)
            .collect::<Vec<usize>>());
        let mut v = self
            .line
            .iter()
            .map(|m| m.num_inspect)
            .collect::<Vec<usize>>();
        v.sort();
        v.reverse();
        v[0] * v[1]
    }
}

impl Puzzle {
    fn thrown(&mut self, items: &mut [Vec<usize>]) {
        for (i, v) in items.iter_mut().enumerate() {
            if !v.is_empty() {
                let mut w = Vec::new();
                std::mem::swap(v, &mut w);
                self.line[i].items.append(&mut w);
            }
        }
    }
}
