//! <https://adventofcode.com/2024/day/14>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        parser::parse_isize,
    },
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{cmp::Ordering, collections::HashMap, hash::BuildHasherDefault},
    winnow::{
        ascii::newline,
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<(isize, isize, isize, isize)>,
    size: (isize, isize),
}

// impl Default for Puzzle {
//     fn default() -> Self {
//         Puzzle { }
//     }
// }

// p=0,4 v=3,-3
fn parse_line(s: &mut &str) -> PResult<(isize, isize, isize, isize)> {
    seq!(_: "p=", parse_isize, _: ",", parse_isize,
    _: " v=", parse_isize, _: ",", parse_isize)
    .map(|(x, y, dx, dy)| (y, x, dy, dx))
    .parse_next(s)
}
fn parse(s: &mut &str) -> PResult<Vec<(isize, isize, isize, isize)>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc(2024, 14)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let s = &mut input.as_str();
        self.line = parse(s)?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        self.size = match &self.get_config().alt {
            Some(x) if x.as_str() == "0" => (7, 11),
            _ => (103, 101),
        };
    }
    fn part1(&mut self) -> Self::Output1 {
        let t = 100;
        let hy = self.size.0 / 2;
        let hx = self.size.1 / 2;
        let res = self
            .line
            .iter()
            .map(|&(pi, pj, si, sj)| {
                let a = (((t * si + pi) % self.size.0) + self.size.0) % self.size.0;
                let b = (((t * sj + pj) % self.size.1) + self.size.1) % self.size.1;
                // println!("{a:>2}, {b:>2}");
                match ((a).cmp(&hy), (b).cmp(&hx)) {
                    (Ordering::Equal, _) | (_, Ordering::Equal) => (0, 0, 0, 0),
                    (Ordering::Less, Ordering::Less) => (1, 0, 0, 0),
                    (Ordering::Less, Ordering::Greater) => (0, 1, 0, 0),
                    (Ordering::Greater, Ordering::Less) => (0, 0, 1, 0),
                    (Ordering::Greater, Ordering::Greater) => (0, 0, 0, 1),
                }
            })
            .fold((0, 0, 0, 0), |acc, val| {
                (acc.0 + val.0, acc.1 + val.1, acc.2 + val.2, acc.3 + val.3)
            });
        dbg!(&res);
        res.0 * res.1 * res.2 * res.3
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
