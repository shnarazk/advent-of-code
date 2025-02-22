//! <https://adventofcode.com/2024/day/7>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashSet, FxHasher},
    serde::Serialize,
    std::{collections::HashSet, hash::BuildHasherDefault},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<(usize, Vec<usize>)>,
}
mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<(usize, Vec<usize>)> {
        seq!(parse_usize, _: ": ", separated(1.., parse_usize, " "),).parse_next(s)
    }

    pub fn parse(str: &mut &str) -> ModalResult<Vec<(usize, Vec<usize>)>> {
        separated(1.., parse_line, newline).parse_next(str)
    }
}

#[aoc(2024, 7)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.par_iter().map(|(val, v)| expands(v, *val)).sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line.par_iter().map(|(val, v)| expands2(v, *val)).sum()
    }
}

fn expands(vec: &[usize], threshold: usize) -> usize {
    fn exp(mut vec: Vec<usize>, subs: FxHashSet<usize>, threshold: usize) -> usize {
        if let Some(&a) = vec.first() {
            vec.remove(0);
            exp(
                vec,
                subs.iter()
                    .flat_map(|x| {
                        [*x + a, *x * a]
                            .iter()
                            .filter(|v| **v <= threshold)
                            .cloned()
                            .collect::<Vec<_>>()
                    })
                    .collect::<FxHashSet<usize>>(),
                threshold,
            )
        } else if subs.contains(&threshold) {
            threshold
        } else {
            0
        }
    }
    let mut args: Vec<usize> = vec.to_vec();
    let mut temp: FxHashSet<usize> = HashSet::<usize, BuildHasherDefault<FxHasher>>::default();
    temp.insert(args.remove(0));
    exp(args, temp, threshold)
}

fn expands2(vec: &[usize], threshold: usize) -> usize {
    fn shift(a: usize, b: usize, b0: usize) -> usize {
        if b0 < 10 {
            a * 10 + b
        } else {
            shift(a * 10, b, b0 / 10)
        }
    }
    fn exp(mut vec: Vec<usize>, subs: FxHashSet<usize>, threshold: usize) -> usize {
        if let Some(&a) = vec.first() {
            vec.remove(0);
            exp(
                vec,
                subs.iter()
                    .flat_map(|x| {
                        [*x + a, *x * a, shift(*x, a, a)]
                            .iter()
                            .filter(|v| **v <= threshold)
                            .cloned()
                            .collect::<Vec<_>>()
                    })
                    .collect::<FxHashSet<usize>>(),
                threshold,
            )
        } else if subs.contains(&threshold) {
            threshold
        } else {
            0
        }
    }
    let mut args: Vec<usize> = vec.to_vec();
    let mut temp: FxHashSet<usize> = HashSet::<usize, BuildHasherDefault<FxHasher>>::default();
    temp.insert(args.remove(0));
    exp(args, temp, threshold)
}
