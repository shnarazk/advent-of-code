//! <https://adventofcode.com/2024/day/13>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::{Dim2, GeometricMath},
        parser::parse_usize,
    },
    rayon::prelude::*,
    serde::Serialize,
    winnow::{
        ModalResult, Parser,
        ascii::newline,
        combinator::{separated, seq},
        token::one_of,
    },
};
type Setting = (Dim2<usize>, Dim2<usize>, Dim2<usize>);

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<Setting>,
}

fn parse_button(s: &mut &str) -> ModalResult<Dim2<usize>> {
    seq!(_: "Button ", _: one_of(['A', 'B']),
        _: ": X+", parse_usize,
        _: ", Y+", parse_usize,
    )
    .parse_next(s)
}

fn parse_prize(s: &mut &str) -> ModalResult<Dim2<usize>> {
    seq!(_: "Prize",
        _: ": X=", parse_usize,
        _: ", Y=", parse_usize,
    )
    .parse_next(s)
}

fn parse_block(s: &mut &str) -> ModalResult<Setting> {
    seq!(parse_button, _: newline, parse_button, _: newline, parse_prize).parse_next(s)
}

fn parse(s: &mut &str) -> ModalResult<Vec<Setting>> {
    separated(1.., parse_block, (newline, newline)).parse_next(s)
}

#[aoc(2024, 13)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parse(&mut input)?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.par_iter().map(|(a, b, g)| solve(g, a, b)).sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .par_iter()
            .map(|(a, b, g)| {
                let gg = g.add((10_000_000_000_000, 10_000_000_000_000));
                solve(&gg, a, b)
            })
            .sum()
    }
}

fn solve(goal: &Dim2<usize>, a: &Dim2<usize>, b: &Dim2<usize>) -> usize {
    // . a.0 * i + b.0 * j = goal.0
    // . a.1 * i + b.1 * j = goal.1
    // i = (goal.0 - b.0 * j) / a.0
    // i = (goal.1 - b.1 * j) / a.1
    // . a.0 * (goal.1 - b.1 * j) / a.1 + b.0 * j = goal.0
    //   . a.0 * (goal.1 - b.1 * j) + a.1 * b.0 * j = a.1 * goal.0
    //   . a.0 * goal.1 - a.0 * b.1 * j + a.1 * b.0 * j = a.1 * goal.0
    //   . (a.1 * b.0 - a.0 * b.1) * j = a.1 * goal.0 - a.0 * goal.1
    //
    // b.0 * j = goal.0 - a.0 * i
    // b.1 * j = goal.1 - a.1 * i
    // b.1 * (goal.0 - a.0 * i) = b.0 * (goal.1 - a.1 * i)
    // b.1 * goal.0 - a.0 * b.1 * i = b.0 * goal.1 - a.1 * b.0 * i
    // (a.1 * b.0 - a.0 * b.1) * i = b.0 * goal.1 - b.1 * goal.0
    if a.1 * b.0 != a.0 * b.1 {
        let tmp1 = (a.1 * b.0).abs_diff(a.0 * b.1);
        let tmp2 = (b.0 * goal.1).abs_diff(b.1 * goal.0);
        let tmp3 = (a.1 * goal.0).abs_diff(a.0 * goal.1);
        let i = tmp2 / tmp1;
        let im = tmp2 % tmp1;
        let j = tmp3 / tmp1;
        let jm = tmp3 % tmp1;
        if im == 0 && jm == 0 {
            return 3 * i + j;
        }
    }
    0
}
