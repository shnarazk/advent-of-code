//! <https://adventofcode.com/2024/day/7>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
    },
    serde::Serialize,
    std::collections::{HashMap, HashSet},
    winnow::{
        ascii::{dec_uint, newline, space1},
        combinator::{repeat_till, separated},
        token::literal,
        PResult, Parser,
    },
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<(usize, Vec<usize>)>,
}

// impl Default for Puzzle {
//     fn default() -> Self {
//         Puzzle { }
//     }
// }

fn parse_usize(str: &mut &str) -> PResult<usize> {
    let a: u64 = dec_uint.parse_next(str)?;
    Ok(a as usize)
}

fn parse_line(str: &mut &str) -> PResult<(usize, Vec<usize>)> {
    let (head, _): (u64, &str) = (dec_uint, ": ").parse_next(str)?;
    let v: Vec<usize> = separated(1.., parse_usize, " ").parse_next(str)?;
    Ok((head as usize, v))
}

fn parse(str: &mut &str) -> PResult<Vec<(usize, Vec<usize>)>> {
    separated(1.., parse_line, newline).parse_next(str)
}

#[aoc(2024, 7)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let p = &mut input.as_str();
        self.line = parse(p)?;
        Ok("".to_string())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|(val, v)| if expands(v).contains(&val) { *val } else { 0 })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .map(|(val, v)| if expands2(v).contains(&val) { *val } else { 0 })
            .sum()
    }
}

fn expands(vec: &[usize]) -> HashSet<usize> {
    fn exp(mut vec: Vec<usize>, subs: HashSet<usize>) -> HashSet<usize> {
        if let Some(&a) = vec.get(0) {
            vec.remove(0);
            exp(
                vec,
                subs.iter()
                    .flat_map(|x| [*x + a, *x * a])
                    .collect::<HashSet<usize>>(),
            )
        } else {
            subs
        }
    }
    let mut args: Vec<usize> = vec.to_vec();
    let mut temp: HashSet<usize> = HashSet::new();
    temp.insert(args.remove(0));
    exp(args, temp)
}

fn expands2(vec: &[usize]) -> HashSet<usize> {
    fn shift(a: usize, b: usize, b0: usize) -> usize {
        if b0 < 10 {
            a * 10 + b
        } else {
            shift(a * 10, b, b0 / 10)
        }
    }
    fn exp(mut vec: Vec<usize>, subs: HashSet<usize>) -> HashSet<usize> {
        if let Some(&a) = vec.get(0) {
            vec.remove(0);
            exp(
                vec,
                subs.iter()
                    .flat_map(|x| [*x + a, *x * a, shift(*x, a, a)])
                    .collect::<HashSet<usize>>(),
            )
        } else {
            subs
        }
    }
    let mut args: Vec<usize> = vec.to_vec();
    let mut temp: HashSet<usize> = HashSet::new();
    temp.insert(args.remove(0));
    exp(args, temp)
}
