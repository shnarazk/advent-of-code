//! <https://adventofcode.com/2025/day/11>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        // geometric::{Dim2, NeighborIter},
    },
    // rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHashSet, FxHasher},
    // serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap, HashSet},
        hash::BuildHasherDefault,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(String, Vec<String>)>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline, space1},
            combinator::{alt, repeat, separated, seq},
        },
    };

    fn parse_name(s: &mut &str) -> ModalResult<String> {
        alpha1.map(|s: &str| s.to_string()).parse_next(s)
    }

    fn parse_line(s: &mut &str) -> ModalResult<(String, Vec<String>)> {
        seq!(parse_name, _: ": ", separated(1.., parse_name, " ")).parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<(String, Vec<String>)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2025, 11)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut table: FxHashSet<(&str, &str)> =
            HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        let mut memo: FxHashMap<(&str, &str), usize> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        for (s, outs) in self.line.iter() {
            for out in outs {
                table.insert((s, out));
                memo.insert((s, out), 1);
            }
        }
        check_path(&table, "you", "out", &mut memo)
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut table: FxHashSet<(&str, &str)> =
            HashSet::<_, BuildHasherDefault<FxHasher>>::default();
        let mut memo: FxHashMap<(&str, &str), (usize, usize, usize)> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        for (s, outs) in self.line.iter() {
            for out in outs {
                table.insert((s, out));
                if ["dac", "fft"].contains(&s.as_str()) {
                    memo.insert((s, out), (1, 0, 0));
                } else {
                    memo.insert((s, out), (1, 0, 0));
                }
            }
        }
        check_path2(&table, "svr", "out", &mut memo).2
    }
}

fn check_path<'a>(
    table: &FxHashSet<(&'a str, &'a str)>,
    from: &'a str,
    to: &'a str,
    memo: &mut FxHashMap<(&'a str, &'a str), usize>,
) -> usize {
    if let Some(n) = memo.get(&(from, to)) {
        return *n;
    }
    let n = table
        .iter()
        .filter(|(f, t)| **f == *from)
        .map(|(_, t)| check_path(table, *t, to, memo))
        .sum::<usize>();
    memo.insert((from, to), n);
    n
}

fn check_path2<'a>(
    table: &FxHashSet<(&'a str, &'a str)>,
    from: &'a str,
    to: &'a str,
    memo: &mut FxHashMap<(&'a str, &'a str), (usize, usize, usize)>,
) -> (usize, usize, usize) {
    if let Some(n) = memo.get(&(from, to)) {
        return *n;
    }
    let mut n = table
        .iter()
        .filter(|(f, t)| **f == *from)
        .map(|(_, t)| check_path2(table, *t, to, memo))
        .fold((0, 0, 0), |acc, l| (acc.0 + l.0, acc.1 + l.1, acc.2 + l.2));
    dbg!(from);
    if ["dac", "fft"].contains(&from) {
        n = (0, n.0, n.1);
        dbg!(n);
    }
    memo.insert((from, to), n);
    n
}
