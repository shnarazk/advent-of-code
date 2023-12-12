//! <https://adventofcode.com/2023/day/12>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(Vec<u8>, Vec<usize>)>,
}

#[aoc(2023, 12)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let mut tuple = (Vec::new(), Vec::new());
        for (i, segment) in block.split(' ').enumerate() {
            if i == 1 {
                let nums = line_parser::to_usizes(segment, ',').unwrap();
                tuple.1 = nums;
            } else {
                let vals = segment
                    .chars()
                    .map(|c| match c {
                        '.' => 0,
                        '#' => 1,
                        '?' => 2,
                        _ => unreachable!(),
                    })
                    .collect::<Vec<u8>>();
                tuple.0 = vals;
            }
        }
        self.line.push(tuple);
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().map(count_possibles).sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}

fn matches(kind: &[u8], seq: &[usize]) -> bool {
    let mut len = 0;
    let mut i = 0;
    for p in kind.iter() {
        if *p == 0 {
            if 0 < len {
                if seq.len() <= i {
                    return false;
                }
                if len != seq[i] {
                    return false;
                }
                i += 1;
                len = 0;
            }
        } else {
            len += 1;
        }
    }
    if 0 < len {
        if seq.len() <= i {
            return false;
        }
        if len != seq[i] {
            return false;
        }
        i += 1;
    }
    i == seq.len()
}

fn count_possibles((kind, seq): &(Vec<u8>, Vec<usize>)) -> usize {
    let num_holes = kind.iter().filter(|n| **n == 2).count();
    (0..2usize.pow(num_holes as u32))
        .map(|nth| {
            let mut target = kind.clone();
            let mut index = 0;
            for p in target.iter_mut() {
                if *p == 2 {
                    *p = (((1 << index) & nth) != 0) as u8;
                    index += 1;
                }
            }
            matches(&target, &seq) as usize
        })
        .sum()
}
