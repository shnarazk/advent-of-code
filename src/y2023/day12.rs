//! <https://adventofcode.com/2023/day/12>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::cmp::Ordering;
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
    line: Vec<(Vec<usize>, Vec<usize>)>,
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
                    .collect::<Vec<usize>>();
                tuple.0 = vals;
            }
        }
        self.line.push(tuple);
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        // self.line.iter().map(count_possibles).sum()
        self.line
            .iter()
            .skip(5)
            .take(1)
            .map(|(k, s)| dbg!(match_sequences(k, s)))
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .take(0)
            .map(|(k, s)| {
                let k5 = (0..5).map(|_| k.clone()).collect::<Vec<_>>().join(&2);
                // println!("{:?}", &k5);
                let s5 = s
                    .iter()
                    .cycle()
                    .take(s.len() * 5)
                    .copied()
                    .collect::<Vec<_>>();
                match_sequences(&k5, &s5)
            })
            .sum()
    }
}

fn matches(kind: &[usize], seq: &[usize]) -> bool {
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

fn count_possibles((kind, seq): &(Vec<usize>, Vec<usize>)) -> usize {
    let num_holes = kind.iter().filter(|n| **n == 2).count();
    (0..2usize.pow(num_holes as u32))
        .map(|nth| {
            let mut target = kind.clone();
            let mut index = 0;
            for p in target.iter_mut() {
                if *p == 2 {
                    *p = (((1 << index) & nth) != 0) as usize;
                    index += 1;
                }
            }
            matches(&target, &seq) as usize
        })
        .sum::<usize>()
}

fn match_sequences(a: &[usize], b: &[usize]) -> usize {
    let x = match_sequences_rec(a, b);
    println!(
        "{:?}/{} => {}",
        a.iter()
            .map(|c| match c {
                0 => '.',
                1 => '#',
                _ => '?',
            })
            .collect::<String>(),
        b.len(),
        x
    );
    x
}

fn match_sequences_rec(a: &[usize], b: &[usize]) -> usize {
    // println!(" => {:?}", &a);
    match (a.is_empty(), b.is_empty()) {
        (true, true) => return dbg!(1),
        (false, true) => return dbg!(a.iter().all(|c| *c == 0) as usize),
        (true, false) => return dbg!(0),
        _ => (),
    }
    if a.len() < b.iter().sum() {
        return 0;
    }
    let beg = a[0];
    let ends_at = a
        .iter()
        .enumerate()
        .find(|(_, c)| **c != beg)
        .map_or(a.len(), |(i, _)| i);
    match beg {
        0 => match_sequences(&a[1..], b),
        1 => match b[0].cmp(&ends_at) {
            Ordering::Less => dbg!(0),
            Ordering::Equal if b[0] == a.len() => 1,
            Ordering::Equal => match a[b[0]] {
                0 => match_sequences(&a[b[0]..], &b[1..]),
                1 => unreachable!(),
                2 => {
                    let mut v = a[b[0]..].to_vec();
                    v[0] = 0;
                    match_sequences(&v, &b[1..])
                }
                _ => unreachable!(),
            },
            Ordering::Greater => {
                if (ends_at..b[0]).all(|i| a[i] != 0) {
                    dbg!(match_sequences(&a[b[0]..], &b[1..]))
                } else {
                    0
                }
            }
        },
        2 => match b[0].cmp(&ends_at) {
            // Ordering::Less => match_sequences(&a[b[0]..], &b[1..]),
            _ => {
                let mut v = a.to_vec();
                v[0] = 0;
                let c0 = match_sequences(&v, b);
                v[0] = 1;
                let c1 = match_sequences(&v, b);
                c0 + c1
            }
        },
        _ => unreachable!(),
    }
}

fn printer(v: &[usize]) {
    println!(
        "{}",
        v.iter()
            .map(|c| match c {
                0 => '.',
                1 => '#',
                _ => '?',
            })
            .collect::<String>()
    )
}
