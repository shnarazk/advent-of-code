//! <https://adventofcode.com/2024/day/5>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser::parse_usize,
    },
    rayon::prelude::*,
    rustc_data_structures::fx::FxHasher,
    serde::Serialize,
    std::{
        collections::{HashMap, HashSet},
        hash::BuildHasherDefault,
    },
    winnow::{
        ModalResult, Parser,
        ascii::newline,
        combinator::{repeat_till, separated},
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    rules: Vec<(usize, usize)>,
    updates: Vec<Vec<usize>>,
}

fn parse_rule(str: &mut &str) -> ModalResult<(usize, usize)> {
    let a: usize = parse_usize.parse_next(str)?;
    let _ = "|".parse_next(str)?;
    let b: usize = parse_usize.parse_next(str)?;
    let _ = newline.parse_next(str)?;
    Ok((a, b))
}

fn parse_rules(str: &mut &str) -> ModalResult<Vec<(usize, usize)>> {
    repeat_till(1.., parse_rule, newline)
        .map(|(v, _)| v)
        .parse_next(str)
}

fn parse_update(str: &mut &str) -> ModalResult<Vec<usize>> {
    separated(1.., parse_usize, ",").parse_next(str)
}

fn parse_updates(str: &mut &str) -> ModalResult<Vec<Vec<usize>>> {
    separated(1.., parse_update, newline).parse_next(str)
}

#[aoc(2024, 5)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.rules = parse_rules(&mut input)?;
        self.updates = parse_updates(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.updates
            .par_iter()
            .filter(|v| {
                let occurs = v
                    .iter()
                    .enumerate()
                    .map(|(i, k)| (*k, i))
                    .collect::<HashMap<usize, usize, BuildHasherDefault<FxHasher>>>();
                self.rules.iter().all(|(a, b)| {
                    let i = occurs.get(a);
                    let j = occurs.get(b);
                    i.is_none() || j.is_none() || i < j
                })
            })
            .map(|v| v[v.len() / 2])
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.updates
            .par_iter()
            .filter(|v| {
                let occurs = v
                    .iter()
                    .enumerate()
                    .map(|(i, k)| (*k, i))
                    .collect::<HashMap<usize, usize, BuildHasherDefault<FxHasher>>>();
                !self.rules.iter().all(|(a, b)| {
                    let i = occurs.get(a);
                    let j = occurs.get(b);
                    i.is_none() || j.is_none() || i < j
                })
            })
            .map(|v| {
                let w = topological_sort(&self.rules, (*v).clone());
                w[w.len() / 2]
            })
            .sum()
    }
}

fn topological_sort(rules: &[(usize, usize)], mut context: Vec<usize>) -> Vec<usize> {
    let uppers = rules
        .par_iter()
        .filter(|(a, b)| context.contains(a) && context.contains(b))
        .map(|(_, b)| *b)
        .collect::<HashSet<usize, BuildHasherDefault<FxHasher>>>();
    let lowers = rules
        .par_iter()
        .filter(|(a, b)| context.contains(a) && context.contains(b))
        .map(|(a, _)| *a)
        .collect::<HashSet<usize, BuildHasherDefault<FxHasher>>>();
    let mut cands = lowers
        .par_iter()
        .filter(|x| !uppers.contains(x))
        .cloned()
        .collect::<Vec<_>>();
    if cands.is_empty() {
        lowers.iter().cloned().collect::<Vec<_>>()
    } else {
        assert_eq!(1, cands.len());
        cands.truncate(1);
        context.retain(|n| *n != cands[0]);
        if !context.is_empty() {
            let mut tmp = topological_sort(rules, context);
            cands.append(&mut tmp);
        }
        cands
    }
}
