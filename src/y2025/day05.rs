//! <https://adventofcode.com/2025/day/5>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        // geometric::{Dim2, neighbors8},
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
    // 1. inclsive: closed range
    // 2. overlapped
    ranges: Vec<(usize, usize)>,
    // if it is in a range, it is called 'fresh'
    availables: Vec<usize>,
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

    fn parse_two_usizes(s: &mut &str) -> ModalResult<(usize, usize)> {
        seq!(parse_usize, "-", parse_usize)
            .parse_next(s)
            .map(|(a, _, b)| (a, b))
    }

    fn parse_block1(s: &mut &str) -> ModalResult<Vec<(usize, usize)>> {
        separated(1.., parse_two_usizes, newline).parse_next(s)
    }
    fn parse_block2(s: &mut &str) -> ModalResult<Vec<usize>> {
        separated(1.., parse_usize, newline).parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<(Vec<(usize, usize)>, Vec<usize>)> {
        seq!(parse_block1, seq!(newline, newline), parse_block2)
            .parse_next(dbg!(s))
            .map(|(a, _, b)| (a, b))
    }
}

#[aoc(2025, 5)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        let (b1, b2) = parser::parse(&mut input)?;
        self.ranges = b1;
        self.availables = b2;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.availables
            .iter()
            .filter(|id| self.ranges.iter().any(|(b, e)| *b <= **id && **id <= *e))
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        // let mut _: FxHashMap<_, _> = HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        2
    }
}
