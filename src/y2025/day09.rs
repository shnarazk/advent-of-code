//! <https://adventofcode.com/2025/day/9>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::{Dim2, NeighborIter},
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
    line: Vec<Dim2<usize>>,
}

mod parser {
    use {
        crate::{geometric::Dim2, parser::parse_usize},
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline, space1},
            combinator::{alt, separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Dim2<usize>> {
        seq!(parse_usize, _: ",", parse_usize)
            .map(|(x, y)| (y, x))
            .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Dim2<usize>>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2025, 9)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        dbg!(&self.line);
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        // let mut _: FxHashMap<_, _> = HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        self.line
            .iter()
            .enumerate()
            .map(|(i, p)| {
                self.line
                    .iter()
                    .skip(i)
                    .map(|q| (p.0.abs_diff(q.0) + 1) * (p.1.abs_diff(q.1) + 1))
                    .max()
                    .expect("!")
            })
            .max()
            .unwrap()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
