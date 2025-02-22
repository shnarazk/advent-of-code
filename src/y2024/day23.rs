//! <https://adventofcode.com/2024/day/23>
use {
    crate::framework::{AdventOfCode, ParseError, aoc_at},
    itertools::Itertools,
    rustc_data_structures::fx::{FxHashSet, FxHasher},
    serde::Serialize,
    std::{collections::HashSet, hash::BuildHasherDefault},
    winnow::{
        ModalResult, Parser,
        ascii::newline,
        combinator::{separated, seq},
        token::one_of,
    },
};

type Node = (char, char);

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    line: Vec<(Node, Node)>,
    nodes: Vec<Node>,
    pair: HashSet<(Node, Node), BuildHasherDefault<FxHasher>>,
    triplet: HashSet<(Node, Node, Node), BuildHasherDefault<FxHasher>>,
}

fn parse_node(s: &mut &str) -> ModalResult<Node> {
    (one_of('a'..='z'), one_of('a'..='z')).parse_next(s)
}
fn parse_line(s: &mut &str) -> ModalResult<(Node, Node)> {
    seq!(parse_node, _:"-", parse_node).parse_next(s)
}

fn parse(s: &mut &str) -> ModalResult<Vec<(Node, Node)>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc_at(2024, 23)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parse(&mut input)?;
        let mut nodes: FxHashSet<Node> = HashSet::<Node, BuildHasherDefault<FxHasher>>::default();
        for (na, nb) in self.line.iter() {
            nodes.insert(*na);
            nodes.insert(*nb);
            self.pair
                .insert(if na < nb { (*na, *nb) } else { (*nb, *na) });
        }
        self.nodes = nodes.iter().sorted().cloned().collect::<Vec<_>>();
        Self::parsed()
    }
    fn serialize(&self) -> Option<String> {
        let data = self
            .line
            .iter()
            .map(|(name1, name2)| {
                (
                    format!("{}{}", name1.0, name1.1),
                    format!("{}{}", name2.0, name2.1),
                )
            })
            .collect::<Vec<_>>();
        serde_json::to_string(&data).ok()
    }
    fn part1(&mut self) -> Self::Output1 {
        for (i, n1) in self.nodes.iter().enumerate() {
            for (j, n2) in self.nodes.iter().enumerate().skip(i + 1) {
                for n3 in self.nodes.iter().skip(j + 1) {
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
        let mut best: FxHashSet<Node> = HashSet::<Node, BuildHasherDefault<FxHasher>>::default();
        for (i, n1) in self.nodes.iter().enumerate() {
            if best.contains(n1) {
                continue;
            }
            let mut tmp: FxHashSet<Node> = HashSet::<Node, BuildHasherDefault<FxHasher>>::default();
            tmp.insert(*n1);
            for n2 in self.nodes.iter().skip(i + 1) {
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
