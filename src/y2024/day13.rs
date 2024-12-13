//! <https://adventofcode.com/2024/day/13>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        parser::{self, parse_usize},
    },
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{collections::HashMap, hash::BuildHasherDefault},
    winnow::{
        ascii::newline,
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<((usize, usize), (usize, usize), (usize, usize))>,
}

fn parse_button(s: &mut &str) -> PResult<(usize, usize)> {
    seq!(_: "Button ", _: one_of(['A', 'B']),
        _: ": X+", parse_usize,
        _: ", Y+", parse_usize,
    )
    .parse_next(s)
}

fn parse_prize(s: &mut &str) -> PResult<(usize, usize)> {
    seq!(_: "Prize",
        _: ": X=", parse_usize,
        _: ", Y=", parse_usize,
    )
    .parse_next(s)
}

fn parse_block(s: &mut &str) -> PResult<((usize, usize), (usize, usize), (usize, usize))> {
    seq!(parse_button, _: newline, parse_button, _: newline, parse_prize).parse_next(s)
}

fn parse(s: &mut &str) -> PResult<Vec<((usize, usize), (usize, usize), (usize, usize))>> {
    separated(1.., parse_block, (newline, newline)).parse_next(s)
}

#[aoc(2024, 13)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let s = &mut input.as_str();
        self.line = parse(s)?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|(a, b, g)| {
                let Some((i, j)) = solve(g, a, b) else {
                    return 0;
                };
                i * 3 + j
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}

fn solve(goal: &(usize, usize), a: &(usize, usize), b: &(usize, usize)) -> Option<(usize, usize)> {
    /*
      . a.0 * i + b.0 * j = goal.0
      . a.1 * i + b.1 * j = goal.1

      i = (goal.0 - b.0 * j) / a.0
      i = (goal.1 - b.1 * j) / a.1

      . a.0 * (goal.1 - b.1 * j) / a.1 + b.0 * j = goal.0
      . a.1 * (goal.0 - b.0 * j) / a.0 + b.1 * j = goal.1

      . a.0 * (goal.1 - b.1 * j) + a.1 * b.0 * j = a.1 * goal.0

      . a.0 * goal.1 - a.0 * b.1 * j + a.1 * b.0 * j = a.1 * goal.0

      . (a.1 * b.0 - a.0 * b.1) * j = (a.1 * goal.0 - a.0 * goal.1)

    */
    if a.1 * b.0 != a.0 * b.1 {
        let tmp1 = (a.1 * b.0).abs_diff(a.0 * b.1);
        let tmp2 = (a.1 * goal.0).abs_diff(a.0 * goal.1);
        if tmp2 % tmp1 == 0 {
            let j = tmp2 / tmp1;
            let i = (goal.0 - b.0 * j) / a.0;
            return Some((i, j));
        }
    }
    None
}
