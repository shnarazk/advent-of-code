//! <https://adventofcode.com/017/day/7>
use {
    crate::framework::{aoc_at, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Tree {
    Leaf(String, usize),
    Node(String, usize, Vec<String>),
}

impl Tree {
    fn node_name(&self) -> &str {
        match self {
            Tree::Leaf(name, _) => name,
            Tree::Node(name, _, _) => name,
        }
    }
    fn node_weight(&self) -> usize {
        match self {
            Tree::Leaf(_, weight) => *weight,
            Tree::Node(_, weight, _) => *weight,
        }
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Puzzle {
    line: Vec<Tree>,
}

mod parser {
    use {
        super::Tree,
        crate::parser::parse_usize,
        winnow::{
            ascii::{alpha1, newline},
            combinator::{alt, separated, seq},
            ModalResult, Parser,
        },
    };

    fn parse_tree(s: &mut &str) -> ModalResult<Tree> {
        alt((
            seq!(alpha1, _: " (", parse_usize, _: ") -> ", separated(1.., alpha1, ", ").map(|v: Vec<&str>| v.iter().map(|s| s.to_string()).collect::<Vec<_>>()))
                            .map(|(s, n, v)| Tree::Node(s.to_string(), n, v)),
            seq!(alpha1, _: " (", parse_usize, _: ")").map(|(s, n)| Tree::Leaf(s.to_string(), n)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Tree>> {
        separated(1.., parse_tree, newline).parse_next(s)
    }
}

#[aoc_at(2017, 7)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = usize;
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut parent: HashMap<String, String> = HashMap::new();
        for node in self.line.iter() {
            if let Tree::Node(name, _, subs) = node {
                for sub in subs.iter() {
                    parent.insert(sub.clone(), name.clone());
                }
            }
        }
        let mut target: &str = self.line[0].node_name();
        while let Some(p) = parent.get(target) {
            target = p;
        }
        target.to_string()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut parent: HashMap<String, String> = HashMap::new();
        let mut tree: HashMap<String, Tree> = HashMap::new();
        for node in self.line.iter() {
            if let Tree::Node(name, _, subs) = node {
                for sub in subs.iter() {
                    parent.insert(sub.clone(), name.clone());
                }
            }
            tree.insert(node.node_name().to_string(), node.clone());
        }
        let mut root: &str = self.line[0].node_name();
        while let Some(p) = parent.get(root) {
            root = p;
        }
        seek(root, &tree).unwrap_or(0)
    }
}

fn seek<'a>(name: &'a str, tree: &'a HashMap<String, Tree>) -> Option<usize> {
    if let Some(Tree::Node(_, _, subs)) = tree.get(name) {
        for s in subs.iter() {
            if let Some(val) = seek(s.as_str(), tree) {
                return Some(val);
            }
        }
        let w = total_weight(&subs[0], tree);
        if !subs[1..].iter().all(|n| total_weight(n, tree) == w) {
            let mut weights: Vec<usize> = Vec::new();
            let mut w_count: HashMap<usize, usize> = HashMap::new();
            for w in subs.iter().map(|s| total_weight(s, tree)) {
                weights.push(w);
                *w_count.entry(w).or_insert(0) += 1;
            }
            for (i, name) in subs.iter().enumerate() {
                if w_count.get(&weights[i]) == Some(&1) {
                    let expected = weights[(i == 0) as usize];
                    // println!(
                    //     "{:?}",
                    //     subs.iter()
                    //         .map(|n| (tree.get(n).unwrap().node_weight(), total_weight(n, tree)))
                    //         .collect::<Vec<_>>()
                    // );
                    return Some(tree.get(name).unwrap().node_weight() + expected - weights[i]);
                }
            }
        }
    }
    None
}

fn total_weight(name: &String, tree: &HashMap<String, Tree>) -> usize {
    let node = tree.get(name).unwrap();
    match node {
        Tree::Leaf(_, weight) => *weight,
        Tree::Node(_, weight, subs) => {
            subs.iter().map(|n| total_weight(n, tree)).sum::<usize>() + *weight
        }
    }
}
