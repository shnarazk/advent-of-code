//! <https://adventofcode.com/2025/day/6>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        // geometric::{Dim2, NeighborIterator},
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Op {
    Add,
    Mul,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    problem: Vec<Vec<usize>>,
    ops: Vec<Op>,
}

mod parser {
    use {
        super::Op,
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline, space0, space1},
            combinator::{alt, preceded, separated, seq},
            token::one_of,
        },
    };

    fn parse_problem(s: &mut &str) -> ModalResult<Vec<usize>> {
        preceded(space0, separated(1.., parse_usize, space1)).parse_next(s)
    }
    fn parse_problems(s: &mut &str) -> ModalResult<Vec<Vec<usize>>> {
        separated(1.., parse_problem, seq!(space0, newline)).parse_next(s)
    }
    fn parse_op(s: &mut &str) -> ModalResult<Op> {
        one_of(['+', '*'])
            .map(|c: char| if c == '+' { Op::Add } else { Op::Mul })
            .parse_next(s)
    }
    fn parse_ops(s: &mut &str) -> ModalResult<Vec<Op>> {
        preceded(space0, separated(1.., parse_op, space1)).parse_next(s)
    }
    pub fn parse(s: &mut &str) -> ModalResult<(Vec<Vec<usize>>, Vec<Op>)> {
        seq!(parse_problems, newline, parse_ops)
            .parse_next(s)
            .map(|(a, _, b)| (a, b))
    }
}

#[aoc(2025, 6)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        let (p, o) = parser::parse(&mut input)?;
        self.problem = p;
        self.ops = o;
        assert_eq!(self.problem[0].len(), self.ops.len());
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.ops
            .iter()
            .enumerate()
            .map(|(i, op)| match op {
                Op::Add => self.problem.iter().map(|v| v[i]).fold(0, |acc, x| acc + x),
                Op::Mul => self.problem.iter().map(|v| v[i]).fold(1, |acc, x| acc * x),
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        // let mut _: FxHashMap<_, _> = HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        2
    }
}
