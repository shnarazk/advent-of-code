//! <https://adventofcode.com/2018/day/7>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{HashMap, HashSet},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(char, char)>,
}

#[aoc_at(2018, 7)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = usize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // Step L must be finished before step X can begin.
        let parser = regex!(r"^Step (\w) must be finished before step (\w) can begin.");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1].chars().next().unwrap(),
            segment[2].chars().next().unwrap(),
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut succs: HashMap<char, Vec<char>> = HashMap::new();
        let mut conds: HashMap<char, Vec<char>> = HashMap::new();
        let mut prev: HashMap<char, char> = HashMap::new();
        let mut letters: HashSet<char> = HashSet::new();
        for rel in self.line.iter() {
            letters.insert(rel.0);
            letters.insert(rel.1);
            succs.entry(rel.0).or_insert(Vec::new()).push(rel.1);
            conds.entry(rel.1).or_insert(Vec::new()).push(rel.0);
            prev.insert(rel.1, rel.0);
        }
        dbg!(letters.len());
        dbg!(succs.len());
        dbg!(prev.len());
        let mut available: Vec<char> = succs
            .keys()
            .filter(|n| prev.get(n).is_none())
            .copied()
            .collect::<Vec<_>>();
        dbg!(&available);
        let mut result: String = String::new();
        loop {
            if available.is_empty() {
                break;
            }
            available.sort();
            let mut c: char = ' ';
            for (i, cand) in available.iter().enumerate() {
                if conds
                    .get(cand)
                    .unwrap_or(&vec![])
                    .iter()
                    .all(|c| result.contains(*c))
                {
                    c = available.remove(i);
                    break;
                }
            }
            if let Some(v) = succs.get(&c) {
                for s in v.iter() {
                    if !available.contains(s) && !result.contains(*s) {
                        available.push(*s);
                    }
                }
            }
            result.push(c);
        }
        dbg!(result.len());
        result
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
