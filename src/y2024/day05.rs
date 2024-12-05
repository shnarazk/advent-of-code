//! <https://adventofcode.com/2024/day/5>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    serde::Serialize,
    std::collections::{HashMap, HashSet},
    winnow::{
        ascii::{dec_uint, newline},
        combinator::{repeat_till, separated},
        token::literal,
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
        self.updates
            .iter()
            .filter(|v| {
                let occurs = v
                    .iter()
                    .enumerate()
                    .map(|(i, k)| (*k, i))
                    .collect::<HashMap<usize, usize>>();
                !self.rules.iter().all(|(a, b)| {
                    let i = occurs.get(a);
                    let j = occurs.get(b);
                    i == None || j == None || i < j
                })
            })
            .map(|v| {
                let w = bubble_sort(&self.rules, (*v).clone());
                w[w.len() / 2]
            })
            .sum()
    }
}

fn bubble_sort(rules: &[(usize, usize)], mut context: Vec<usize>) -> Vec<usize> {
    let uppers = rules
        .iter()
        .filter(|(a, b)| context.contains(a) && context.contains(b))
        .map(|(_, b)| *b)
        .collect::<HashSet<usize>>();
    let lowers = rules
        .iter()
        .filter(|(a, b)| context.contains(a) && context.contains(b))
        .map(|(a, _)| *a)
        .collect::<HashSet<usize>>();
    let mut cands = lowers
        .iter()
        .filter(|x| !uppers.contains(&x))
        .cloned()
        .collect::<Vec<_>>();
    if cands.is_empty() {
        return lowers.iter().cloned().collect::<Vec<_>>();
    } else {
        assert_eq!(1, cands.len());
        cands.truncate(1);
        context.retain(|n| *n != cands[0]);
        if !context.is_empty() {
            let mut tmp = bubble_sort(rules, context);
            cands.append(&mut tmp);
        }
        cands
    }
}
