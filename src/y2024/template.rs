//! <https://adventofcode.com/2024/day/0>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
    },
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap},
        hash::BuildHasherDefault,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<()>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ascii::{alpha1, newline, space1},
            combinator::{alt, separated, seq},
            ModalResult, Parser,
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<()> {
        ().parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<()>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2024, 0)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        // let mut _: FxHashMap<_, _> = HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        1
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
