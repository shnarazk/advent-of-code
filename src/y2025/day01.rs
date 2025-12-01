//! <https://adventofcode.com/2025/day/1>
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
    line: Vec<isize>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline, space1},
            combinator::{alt, separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<isize> {
        seq!(alt(("L", "R")), parse_usize)
            .parse_next(s)
            .map(|(s, n)| (n as isize) * if s == "L" { -1 } else { 1 })
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<isize>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2025, 1)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut pos: isize = 50;
        let mut zeros: usize = 0;
        for a in self.line.iter() {
            pos = (pos + a) % 100;
            zeros += (pos == 0) as usize;
        }
        zeros
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut pos: isize = 50;
        let mut zeros: usize = 0;
        for a in self.line.iter() {
            let old = pos;
            pos += a;
            zeros += (old > 0 && pos <= 0) as usize;
            zeros += pos.unsigned_abs() / 100;
            pos = pos.rem_euclid(100);
        }
        zeros
    }
}
