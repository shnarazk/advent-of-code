//! <https://adventofcode.com/2024/day/19>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    rayon::prelude::*,
    serde::Serialize,
    winnow::{
        ModalResult, Parser,
        ascii::newline,
        combinator::{repeat, separated, seq},
        token::one_of,
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
    fn matchable(&self, design: &[Kind]) -> bool {
        let mut checked: Vec<Option<bool>> = vec![None; design.len() + 1];
        checked[design.len()] = Some(true);
        self.matchable_aux(design, 0, &mut checked)
    }
    fn matchable_aux(&self, design: &[Kind], from: usize, checked: &mut [Option<bool>]) -> bool {
        if let Some(b) = checked[from] {
            return b;
        }
        for towel in self.pattern.iter() {
            if design[from..].starts_with(towel)
                && self.matchable_aux(design, from + towel.len(), checked)
            {
                checked[from] = Some(true);
                return true;
            }
        }
        checked[from] = Some(false);
        false
    }
    fn count(&self, design: &[Kind]) -> usize {
        let mut checked: Vec<Option<usize>> = vec![None; design.len() + 1];
        checked[design.len()] = Some(1);
        self.count_aux(design, 0, &mut checked)
    }
    fn count_aux(&self, design: &[Kind], from: usize, checked: &mut [Option<usize>]) -> usize {
        if let Some(n) = checked[from] {
            return n;
        }
        let c = self
            .pattern
            .iter()
            .filter(|pattern| design[from..].starts_with(pattern))
            .map(|p| self.count_aux(design, from + p.len(), checked))
            .sum::<usize>();
        checked[from] = Some(c);
        c
    }
}

fn parse_kind(s: &mut &str) -> ModalResult<Kind> {
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

fn parse_subpattern(s: &mut &str) -> ModalResult<Vec<Kind>> {
    repeat(1.., parse_kind).parse_next(s)
}
fn parse_pattern(s: &mut &str) -> ModalResult<Vec<Vec<Kind>>> {
    separated(1.., parse_subpattern, ", ").parse_next(s)
}

fn parse_design(s: &mut &str) -> ModalResult<Vec<Kind>> {
    repeat(1.., parse_kind).parse_next(s)
}

#[allow(clippy::type_complexity)]
fn parse(s: &mut &str) -> ModalResult<(Vec<Vec<Kind>>, Vec<Vec<Kind>>)> {
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
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        let (pattern, designs) = parse(&mut input)?;
        self.pattern = pattern;
        self.designs = designs;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.designs
            .par_iter()
            .filter(|d| self.matchable(d))
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.designs
            .par_iter()
            .map(|d| self.count(d))
            .sum::<usize>()
    }
}
