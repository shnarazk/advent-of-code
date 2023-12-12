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
        self.line
            .iter()
            .take(0)
            .map(|(k, s)| {
                let k5 = k
                    .iter()
                    .cycle()
                    .take(k.len() * 5)
                    .copied()
                    .collect::<Vec<_>>();
                let s5 = s
                    .iter()
                    .cycle()
                    .take(s.len() * 5)
                    .copied()
                    .collect::<Vec<_>>();
                count_possibles(&(k5, s5))
            })
            .sum()
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
        .sum::<usize>()
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Range {
    unc: usize,
    len: usize,
}

fn trim(mut a: Vec<Range>, mut b: Vec<Range>) -> (Vec<Range>, Vec<Range>) {
    //
    if a[0].unc == 0 && b[0].unc == 0 && a[0].len == 0 && b[0].len == 0 {
        a.remove(0);
        b.remove(0);
    }
    let a_lst = a.len() - 1;
    let b_lst = b.len() - 1;
    if a[a_lst].unc == 0 && b[b_lst].unc == 0 && a[a_lst].len == 0 && b[b_lst].len == 0 {
        a.remove(a_lst);
        b.remove(b_lst);
    }
    (a, b)
}

fn match_seq(a: Vec<Range>, b: Vec<Range>) -> Option<usize> {
    None
}

