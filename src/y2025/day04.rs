//! <https://adventofcode.com/2025/day/4>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::{neighbors, neighbors8},
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
    line: Vec<Vec<bool>>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline, space1},
            combinator::{alt, repeat, repeat_till, separated, seq},
            token::one_of,
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Vec<bool>> {
        repeat(1.., one_of(['.', '@']).map(|c: char| c == '@')).parse_next(s)
    }
    pub fn parse(s: &mut &str) -> ModalResult<Vec<Vec<bool>>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2025, 4)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut found: usize = 0;
        let height = self.line.len();
        let width = self.line[0].len();
        for (i, l) in self.line.iter().enumerate() {
            for (j, b) in l.iter().enumerate() {
                if *b
                    && neighbors8(i, j, height, width)
                        .iter()
                        .filter(|(i, j)| self.line[*i][*j])
                        .count()
                        < 4
                {
                    found += 1;
                }
            }
        }
        found
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
