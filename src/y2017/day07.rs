//! <https://adventofcode.com/2017/day/7>
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

#[derive(Debug, Default, Eq, Hash, PartialEq)]
pub struct Puzzle {
    line: Vec<Tree>,
}

#[aoc(2017, 7)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // dqyjg (65)
        let parser1 = regex!(r"^(\w+) \((\d+)\)$");
        // pqtboz (207) -> ayvns, codwosk
        let parser2 = regex!(r"^(\w+) \((\d+)\) -> ((\w+, )+\w+)$");
        if let Some(segment) = parser1.captures(block) {
            self.line.push(Tree::Leaf(
                segment[1].to_string(),
                segment[2].parse::<usize>()?,
            ));
        } else if let Some(segment) = parser2.captures(block) {
            self.line.push(Tree::Node(
                segment[1].to_string(),
                segment[2].parse::<usize>()?,
                segment[3]
                    .split(", ")
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>(),
            ))
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut parent: HashMap<String, String> = HashMap::new();
        for node in self.line.iter() {
            match node {
                Tree::Leaf(name, _) => (),
                Tree::Node(name, _, subs) => {
                    for sub in subs.iter() {
                        parent.insert(sub.clone(), name.clone());
                    }
                }
            }
        }
        let mut target: &str = self.line[0].node_name();
        while let Some(p) = parent.get(target) {
            target = p;
        }
        dbg!(target);
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut parent: HashMap<String, String> = HashMap::new();
        let mut tree: HashMap<String, Tree> = HashMap::new();
        for node in self.line.iter() {
            match node {
                Tree::Leaf(name, _) => (),
                Tree::Node(name, _, subs) => {
                    for sub in subs.iter() {
                        parent.insert(sub.clone(), name.clone());
                    }
                }
            }
            tree.insert(node.node_name().to_string(), node.clone());
        }
        let mut root: &str = self.line[0].node_name();
        while let Some(p) = parent.get(root) {
            root = p;
        }
        seek(root, &tree);
        0
    }
}

fn seek<'a>(name: &'a str, tree: &'a HashMap<String, Tree>) -> bool {
    dbg!(name);
    if let Some(Tree::Node(_, weight, subs)) = tree.get(name) {
        if subs.iter().any(|s| seek(s.as_str(), tree)) {
            return true;
        }
        let w = total_weight(subs[0].as_str(), tree);
        if !subs[1..]
            .iter()
            .all(|n| total_weight(n.as_str(), tree) == w)
        {
            println!(
                "{:?}",
                subs.iter()
                    .map(|n| (
                        tree.get(n).unwrap().node_weight(),
                        total_weight(n.as_str(), tree)
                    ))
                    .collect::<Vec<_>>()
            );
            return true;
        }
    }
    false
}

fn total_weight(name: &str, tree: &HashMap<String, Tree>) -> usize {
    let node = tree.get(name).unwrap();
    match node {
        Tree::Leaf(_, weight) => *weight,
        Tree::Node(_, weight, subs) => {
            subs.iter()
                .map(|n| total_weight(n.as_str(), tree))
                .sum::<usize>()
                + *weight
        }
    }
}
