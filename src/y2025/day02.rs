//! <https://adventofcode.com/2025/day/2>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::neighbors,
    },
    // rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    // serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap},
        hash::BuildHasherDefault,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline, space1},
            combinator::{separated, seq},
        },
    };
    fn parse_line(s: &mut &str) -> ModalResult<(usize, usize)> {
        seq!(parse_usize, "-", parse_usize)
            .parse_next(s)
            .map(|(a, _, b)| (a, b))
    }
    pub fn parse(s: &mut &str) -> ModalResult<Vec<(usize, usize)>> {
        separated(1.., parse_line, ",").parse_next(s)
    }
}

#[aoc(2025, 2)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut found = 0;
        for (s, e) in self.line.iter() {
            for n in *s..=*e {
                if satisfies(n) {
                    // dbg!(n);
                    found += n;
                };
            }
            // satisfies(*s);
        }
        // dbg!(satisfies(11));
        // dbg!(satisfies(12));
        // dbg!(satisfies(311));
        // dbg!(satisfies(310));
        // dbg!(satisfies(123231));
        // dbg!(satisfies(1230231));
        // dbg!(satisfies(15133));
        found
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut found = 0;
        for (s, e) in self.line.iter() {
            println!("{s}-{}", s.abs_diff(*e));
            for n in *s..=*e {
                if satisfies2(n) {
                    dbg!(n);
                    found += n;
                };
            }
        }
        found
    }
}

fn satisfies(n: usize) -> bool {
    let v = vectorize(n);
    if v.len() % 2 == 1 {
        return false;
    }
    let offset = v.len() / 2;
    v[..offset]
        .iter()
        .enumerate()
        .all(|(i, n)| *n == v[offset + i])
    // dbg!(&v);
    /*
    let distance = v
        .iter()
        .enumerate()
        .map(|(i, d)| {
            v[i + 1..]
                .iter()
                .position(|x| *x == *d)
                .map_or(0, |s| s + 1)
        })
        .collect::<Vec<_>>();
    // dbg!(&distance);
    distance.iter().enumerate().any(|(i, d)| {
        v[i] > 0 && *d > 0 && i + d < v.len() && distance[i + 1..i + *d].iter().all(|x| *x == *d)
    })
    */
}

fn satisfies2(n: usize) -> bool {
    let v = vectorize(n);
    'next: for m in 2..=v.len().max(2) {
        if v.len() % m == 0 {
            let l = v.len() / m;
            for (i, d) in v.iter().take(l).enumerate() {
                if !(1..m).all(|r| v[i + r * l] == *d) {
                    continue 'next;
                }
            }
            return true;
        }
    }
    false
}

fn vectorize(mut n: usize) -> Vec<usize> {
    let mut v: Vec<usize> = Vec::new();
    while n > 0 {
        v.push(n % 10);
        n /= 10;
    }
    v.reverse();
    v
}
