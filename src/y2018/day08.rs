//! <https://adventofcode.com/2018/day/8>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<usize>,
}

#[aoc(2018, 8)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = parser::to_usizes(block, &[' '])?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.build_span(0).1
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut table: HashMap<usize, Metadata> = HashMap::new();
        self.build_table(0, &mut table);
        sum_meta(0, &table)
    }
}

#[derive(Debug, Eq, PartialEq)]
enum Metadata {
    Leaf(usize),
    Link(Vec<usize>),
}

impl Puzzle {
    /// return:
    /// - the index of the next entry
    /// - and the sum of metadatas in this range
    fn build_span(&self, index: usize) -> (usize, usize) {
        let num_children = self.line[index];
        let num_metadata = self.line[index + 1];
        let mut sum_metas = 0;
        let mut i = index + 2;
        for _ in 0..num_children {
            let tmp = self.build_span(i);
            i = tmp.0;
            sum_metas += tmp.1;
        }
        for m in 0..num_metadata {
            sum_metas += self.line[i + m];
        }
        (i + num_metadata, sum_metas)
    }
    fn build_table(&self, index: usize, table: &mut HashMap<usize, Metadata>) -> usize {
        let num_children = self.line[index];
        let num_metadata = self.line[index + 1];
        let mut i = index + 2;
        let mut child_indexes = Vec::new();
        for _ in 0..num_children {
            child_indexes.push(i);
            i = self.build_table(i, table);
        }
        if num_children == 0 {
            let metas: usize = self.line[i..i + num_metadata].iter().sum();
            table.insert(index, Metadata::Leaf(metas));
        } else {
            let mut metas: Vec<usize> = Vec::new();
            for j in &self.line[i..i + num_metadata] {
                if *j == 0 {
                    continue;
                }
                if let Some(k) = child_indexes.get(*j - 1) {
                    metas.push(*k);
                }
            }
            table.insert(index, Metadata::Link(metas));
        }
        i + num_metadata
    }
}

fn sum_meta(index: usize, table: &HashMap<usize, Metadata>) -> usize {
    match table.get(&index) {
        Some(Metadata::Leaf(n)) => *n,
        Some(Metadata::Link(v)) => v.iter().map(|n| sum_meta(*n, table)).sum(),
        None => 0,
    }
}
