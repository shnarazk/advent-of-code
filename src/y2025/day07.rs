//! <https://adventofcode.com/2025/day/7>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::{Dim2, NeighborIterator},
    },
    // rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    // serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap, HashSet},
        hash::BuildHasherDefault,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
    start: Dim2<usize>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline, space1},
            combinator::{alt, repeat, separated, seq},
            token::one_of,
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Vec<char>> {
        repeat(1.., one_of(['.', '^', 'S'])).parse_next(s)
    }
    pub fn parse(s: &mut &str) -> ModalResult<Vec<Vec<char>>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2025, 7)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        'end: for (i, l) in self.line.iter().enumerate() {
            for (j, c) in l.iter().enumerate() {
                if *c == 'S' {
                    self.start = (i, j);
                    break 'end;
                }
            }
        }
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let height = self.line.len();
        let width = self.line[0].len();
        // let mut _: FxHashMap<_, _> = HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        let mut pos: HashSet<usize> = HashSet::new();
        pos.insert(self.start.1);
        let mut next: HashSet<usize> = HashSet::new();
        let mut num_splits = 0;
        for y in self.start.0..height {
            next.clear();
            for x in pos.iter() {
                if self.line[y][*x] == '^' {
                    num_splits += 1;
                    if 0 < *x {
                        next.insert(x - 1);
                    }
                    if x + 1 < width {
                        next.insert(x + 1);
                    }
                } else {
                    next.insert(*x);
                }
            }
            std::mem::swap(&mut pos, &mut next);
        }
        num_splits
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
