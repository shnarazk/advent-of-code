//! <https://adventofcode.com/2022/day/11>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser::parse_usize,
    },
    winnow::{
        ModalResult, Parser,
        ascii::{newline, space1},
        combinator::{alt, separated, seq},
        token::one_of,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
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

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Monkey>,
}

fn parse_operation_target(s: &mut &str) -> ModalResult<Option<usize>> {
    alt(("old".map(|_a| None), parse_usize.map(Some))).parse_next(s)
}

fn parse_block(s: &mut &str) -> ModalResult<Monkey> {
    seq!(
        _: "Monkey ", parse_usize, _: ":",
        _: "\n  Starting items: ", separated(1.., parse_usize, ", "),
        _: "\n  Operation: new = old ", one_of(['*', '+']), _: space1, parse_operation_target,
        _: "\n  Test: divisible by ", parse_usize,
        _: "\n    If true: throw to monkey ", parse_usize,
        _: "\n    If false: throw to monkey ", parse_usize,
        _: newline
    )
    .map(|(id, items, op, num1, test, test_then, test_else)| Monkey {
        id,
        items,
        operation: (op == '*', num1),
        test,
        test_then,
        test_else,
        ..Default::default()
    })
    .parse_next(s)
}

fn parse(s: &mut &str) -> ModalResult<Vec<Monkey>> {
    separated(1.., parse_block, newline).parse_next(s)
}

#[aoc(2022, 11)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parse(&mut input)?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut tmp = vec![Vec::new(); self.line.len()];
        for _ in 0..20 {
            for i in 0..self.line.len() {
                let m = &mut self.line[i];
                m.update(&mut tmp);
                self.thrown(&mut tmp);
            }
            // println!(
            //     "{:?}",
            //     self.line.iter().map(|m| &m.items).collect::<Vec<_>>()
            // );
        }
        // dbg!(self
        //     .line
        //     .iter()
        //     .map(|m| m.num_inspect)
        //     .collect::<Vec<usize>>());
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
        // dbg!(self
        //     .line
        //     .iter()
        //     .map(|m| m.num_inspect)
        //     .collect::<Vec<usize>>());
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
