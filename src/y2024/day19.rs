//! <https://adventofcode.com/2024/day/19>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        parser::parse_usize,
    },
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap},
        hash::BuildHasherDefault,
    },
    winnow::{
        ascii::newline,
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub enum Kind {
    White,
    Blue,
    Black,
    Red,
    Green,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    pattern: Vec<Vec<Kind>>,
    designs: Vec<Vec<Kind>>,
}

impl Puzzle {
    fn matchable(&self, design: &[Kind], from: usize, checked: &mut [bool]) -> bool {
        for towel in self.pattern.iter() {
            if design[from..].starts_with(&towel) {
                let remain = from + towel.len();
                if remain == design.len() {
                    return true;
                }
                if !checked[remain] {
                    if self.matchable(design, remain, checked) {
                        return true;
                    }
                    checked[remain] = true;
                }
            }
        }
        false
    }
}

fn parse_kind(s: &mut &str) -> PResult<Kind> {
    one_of(&['w', 'u', 'b', 'r', 'g'])
        .map(|c| match c {
            'w' => Kind::White,
            'u' => Kind::Blue,
            'b' => Kind::Black,
            'r' => Kind::Red,
            'g' => Kind::Green,
            _ => unreachable!(),
        })
        .parse_next(s)
}

fn parse_subpattern(s: &mut &str) -> PResult<Vec<Kind>> {
    repeat(1.., parse_kind).parse_next(s)
}
fn parse_pattern(s: &mut &str) -> PResult<Vec<Vec<Kind>>> {
    separated(1.., parse_subpattern, ", ").parse_next(s)
}

fn parse_design(s: &mut &str) -> PResult<Vec<Kind>> {
    repeat(1.., parse_kind).parse_next(s)
}

fn parse(s: &mut &str) -> PResult<(Vec<Vec<Kind>>, Vec<Vec<Kind>>)> {
    seq!(
        parse_pattern,
        _: newline,
        _: newline,
        separated(1.., parse_design, newline)
    )
    .parse_next(s)
}

#[aoc(2024, 19)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let (pattern, designs) = parse(&mut input.as_str())?;
        self.pattern = pattern;
        self.designs = designs;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        dbg!(&self.designs.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        // let mut _: FxHashMap<_, _> = HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        self.designs
            .par_iter()
            .filter(|d| self.matchable(d, 0, &mut vec![false; d.len()]))
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
