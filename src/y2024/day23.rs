//! <https://adventofcode.com/2024/day/23>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::neighbors,
        parser::parse_usize,
    },
    itertools::Itertools,
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap, HashSet},
        hash::BuildHasherDefault,
    },
    winnow::{
        ascii::newline,
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

type Node = (char, char);

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    line: Vec<(Node, Node)>,
    nodes: Vec<Node>,
    pair: HashSet<(Node, Node)>,
    triplet: HashSet<(Node, Node, Node)>,
}

// fn parse_letter(s: &mut &str) -> PResult<char> {
//     ('a'..='z').parse_next(s)
// }

fn parse_node(s: &mut &str) -> PResult<Node> {
    (one_of('a'..='z'), one_of('a'..='z')).parse_next(s)
}
fn parse_line(s: &mut &str) -> PResult<(Node, Node)> {
    seq!(parse_node, _:"-", parse_node).parse_next(s)
}

fn parse(s: &mut &str) -> PResult<Vec<(Node, Node)>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc_at(2024, 23)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        dbg!(&self.line.len());
        let mut nodes: HashSet<Node> = HashSet::new();
        for (na, nb) in self.line.iter() {
            nodes.insert(*na);
            nodes.insert(*nb);
            self.pair
                .insert(if na < nb { (*na, *nb) } else { (*nb, *na) });
        }
        dbg!(&self.nodes.len());
        self.nodes = nodes.iter().sorted().cloned().collect::<Vec<_>>();
    }
    fn part1(&mut self) -> Self::Output1 {
        for (i, n1) in self.nodes.iter().enumerate() {
            for (j, n2) in self.nodes.iter().enumerate().skip(i + 1) {
                for (k, n3) in self.nodes.iter().enumerate().skip(j + 1) {
                    if self.pair.contains(&(*n1, *n2))
                        && self.pair.contains(&(*n1, *n3))
                        && self.pair.contains(&(*n2, *n3))
                    {
                        self.triplet.insert((*n1, *n2, *n3));
                    }
                }
            }
        }
        self.triplet
            .iter()
            .filter(|(a, b, c)| a.0 == 't' || b.0 == 't' || c.0 == 't')
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut best: HashSet<Node> = HashSet::new();
        for (i, n1) in self.nodes.iter().enumerate() {
            if best.contains(n1) {
                continue;
            }
            let mut tmp: HashSet<Node> = HashSet::new();
            tmp.insert(*n1);
            for (j, n2) in self.nodes.iter().enumerate().skip(i + 1) {
                if tmp.iter().all(|n| self.pair.contains(&(*n, *n2))) {
                    tmp.insert(*n2);
                }
            }
            if best.len() < tmp.len() {
                best = tmp;
            }
        }
        best.iter()
            .sorted()
            .map(|n| format!("{}{}", n.0, n.1))
            .join(",")
    }
}
