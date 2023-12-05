//! <https://adventofcode.com/2023/day/5>
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

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    seeds: Vec<usize>,
    line: Vec<Vec<(usize, usize, usize)>>,
}

#[aoc(2023, 5)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let mut v = Vec::new();
        for (i, line) in block.trim().split('\n').enumerate() {
            if line.starts_with("seeds:") {
                let vals = line.split(": ").nth(1).unwrap().trim();
                self.seeds = line_parser::to_usizes(vals, ' ')?;
                continue;
            }
            if i == 0 {
                continue;
            }
            let t = line_parser::to_usizes(line, ' ')?;
            v.push((t[0], t[1], t[2]));
        }
        self.line.push(v);
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut locs = self.seeds.clone();
        let map = |pos: usize, dest: usize, source: usize, range: usize| {
            (source <= pos && pos < source + range).then(|| dest + pos - source)
        };
        for (i, trans) in self.line.iter().enumerate() {
            for p in locs.iter_mut() {
                for (d, s, r) in trans.iter() {
                    if let Some(d) = map(*p, *d, *s, *r) {
                        *p = d;
                        break;
                    }
                }
            }
            dbg!(&locs);
        }
        dbg!(*locs.iter().min().unwrap())
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
