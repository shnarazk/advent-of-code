//! <https://adventofcode.com/2024/day/24>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        parser::parse_usize,
    },
    core::prelude,
    itertools::Itertools,
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap},
        default,
        hash::BuildHasherDefault,
        ops::Bound,
    },
    winnow::{
        ascii::newline,
        combinator::{alt, repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

type Wire = (char, char, char);

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
enum Gate {
    #[default]
    And,
    Or,
    Xor,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    wire: Vec<(Wire, bool)>,
    link: Vec<(Gate, Wire, Wire, Wire)>,
    value: FxHashMap<Wire, bool>,
}

impl Puzzle {
    // returns `true` if a now propagaton occured.
    fn evaluate(&mut self, g: Gate, input1: &Wire, input2: &Wire, output: &Wire) -> Option<Wire> {
        let Some(&b1) = self.value.get(input1) else {
            return None;
        };
        let Some(&b2) = self.value.get(input2) else {
            return None;
        };
        let unassigned = self.value.get(output).is_none();
        match g {
            Gate::And => self.value.insert(*output, b1 & b2),
            Gate::Or => self.value.insert(*output, b1 | b2),
            Gate::Xor => self.value.insert(*output, b1 ^ b2),
        };
        unassigned.then(|| *output)
    }
}

fn parse_wire(s: &mut &str) -> PResult<Wire> {
    (
        one_of('a'..='z'),
        one_of(('a'..='z', '0'..='9')),
        one_of(('a'..='z', '0'..='9')),
    )
        .parse_next(s)
}
fn parse_gate(s: &mut &str) -> PResult<Gate> {
    alt(("AND", "OR", "XOR"))
        .map(|g| match g {
            "AND" => Gate::And,
            "OR" => Gate::Or,
            "XOR" => Gate::Xor,
            _ => unreachable!(),
        })
        .parse_next(s)
}

fn parse_setting(s: &mut &str) -> PResult<(Wire, bool)> {
    seq!(parse_wire, _: ": ", parse_usize)
        .map(|(w, b)| (w, b == 1))
        .parse_next(s)
}

fn parse_connection(s: &mut &str) -> PResult<(Gate, Wire, Wire, Wire)> {
    seq!(parse_wire, _: " ", parse_gate, _: " ", parse_wire, _: " -> ", parse_wire)
        .map(|(in1, g, in2, out)| (g, in1, in2, out))
        .parse_next(s)
}

fn parse(s: &mut &str) -> PResult<(Vec<(Wire, bool)>, Vec<(Gate, Wire, Wire, Wire)>)> {
    seq!(
        separated(1.., parse_setting, newline),
        _: (newline, newline),
        separated(1.., parse_connection, newline)
    )
    .parse_next(s)
}

#[aoc(2024, 24)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let (wires, links) = parse(&mut input.as_str())?;
        self.wire = wires;
        self.link = links;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        dbg!(&self.link.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        for (w, b) in self.wire.iter() {
            self.value.insert(*w, *b);
        }
        let mut propagated = true;
        let links = self.link.clone();
        while propagated {
            propagated = false;
            for g in links.iter() {
                if self.evaluate(g.0, &g.1, &g.2, &g.3).is_some() {
                    propagated = true;
                }
            }
        }
        self.value
            .iter()
            .filter(|(wire, _)| wire.0 == 'z')
            .sorted()
            .rev()
            .map(|(_, b)| b)
            .fold(0_usize, |acc, b| acc * 2 + (*b as usize))
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
