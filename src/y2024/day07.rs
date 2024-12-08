//! <https://adventofcode.com/2024/day/7>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser::parse_usize,
    },
    serde::Serialize,
    std::collections::HashSet,
    winnow::{ascii::newline, combinator::separated, PResult, Parser},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<(usize, Vec<usize>)>,
}

fn parse_line(str: &mut &str) -> PResult<(usize, Vec<usize>)> {
    let (head, _): (usize, &str) = (parse_usize, ": ").parse_next(str)?;
    let v: Vec<usize> = separated(1.., parse_usize, " ").parse_next(str)?;
    Ok((head, v))
}

fn parse(str: &mut &str) -> PResult<Vec<(usize, Vec<usize>)>> {
    separated(1.., parse_line, newline).parse_next(str)
}

#[aoc(2024, 7)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let p = &mut input.as_str();
        self.line = parse(p)?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|(val, v)| {
                if expands(v, *val).contains(val) {
                    *val
                } else {
                    0
                }
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .map(|(val, v)| {
                if expands2(v, *val).contains(val) {
                    *val
                } else {
                    0
                }
            })
            .sum()
    }
}

fn expands(vec: &[usize], threshold: usize) -> HashSet<usize> {
    fn exp(mut vec: Vec<usize>, subs: HashSet<usize>, threshold: usize) -> HashSet<usize> {
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
                    .collect::<HashSet<usize>>(),
                threshold,
            )
        } else {
            subs
        }
    }
    let mut args: Vec<usize> = vec.to_vec();
    let mut temp: HashSet<usize> = HashSet::new();
    temp.insert(args.remove(0));
    exp(args, temp, threshold)
}

fn expands2(vec: &[usize], threshold: usize) -> HashSet<usize> {
    fn shift(a: usize, b: usize, b0: usize) -> usize {
        if b0 < 10 {
            a * 10 + b
        } else {
            shift(a * 10, b, b0 / 10)
        }
    }
    fn exp(mut vec: Vec<usize>, subs: HashSet<usize>, threshold: usize) -> HashSet<usize> {
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
                    .collect::<HashSet<usize>>(),
                threshold,
            )
        } else {
            subs
        }
    }
    let mut args: Vec<usize> = vec.to_vec();
    let mut temp: HashSet<usize> = HashSet::new();
    temp.insert(args.remove(0));
    exp(args, temp, threshold)
}
