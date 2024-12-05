//! <https://adventofcode.com/2024/day/5>
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
        ascii::{alpha1, alphanumeric1, dec_uint, digit1, newline},
        combinator::{repeat_till, separated, separated_pair, terminated},
        token::{any, literal, take},
        PResult, Parser,
    },
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    rules: Vec<(usize, usize)>,
    updates: Vec<Vec<usize>>,
}

fn parse_rule(str: &mut &str) -> PResult<(usize, usize)> {
    let a: u64 = dec_uint.parse_next(str)?;
    let _ = literal("|").parse_next(str)?;
    let b: u64 = dec_uint.parse_next(str)?;
    let _ = newline.parse_next(str)?;
    Ok((a as usize, b as usize))
}

fn parse_rules(str: &mut &str) -> PResult<Vec<(usize, usize)>> {
    let (v, _) = repeat_till(1.., parse_rule, newline).parse_next(str)?;
    Ok(v)
}

fn parse_usize(str: &mut &str) -> PResult<usize> {
    let a: u64 = dec_uint.parse_next(str)?;
    Ok(a as usize)
}

fn parse_update(str: &mut &str) -> PResult<Vec<usize>> {
    let v: Vec<usize> = separated(1.., parse_usize, literal(",")).parse_next(str)?;
    Ok(v)
}

fn parse_updates(str: &mut &str) -> PResult<Vec<Vec<usize>>> {
    let v = separated(1.., parse_update, newline).parse_next(str)?;
    Ok(v)
}

#[aoc(2024, 5)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let p = &mut input.as_str();
        self.rules = parse_rules(p)?;
        self.updates = parse_updates(p)?;
        Ok("".to_string())
    }
    fn part1(&mut self) -> Self::Output1 {
        let orders = self
            .rules
            .iter()
            .cloned()
            .collect::<HashSet<(usize, usize)>>();
        dbg!(&orders);
        self.updates
            .iter()
            .filter(|v| {
                let occurs = v
                    .iter()
                    .enumerate()
                    .map(|(i, k)| (*k, i))
                    .collect::<HashMap<usize, usize>>();
                self.rules.iter().all(|(a, b)| {
                    let i = occurs.get(a);
                    let j = occurs.get(b);
                    i == None || j == None || i < j
                })
            })
            .map(|v| v[v.len() / 2])
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
