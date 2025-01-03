//! <https://adventofcode.com/2024/day/1>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser::parse_usize,
    },
    itertools::Itertools,
    serde::Serialize,
    std::collections::HashMap,
    winnow::{
        ascii::{dec_uint, newline, space1},
        combinator::{repeat, seq},
        PResult, Parser,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
}

fn parse(str: &mut &str) -> PResult<Vec<(usize, usize)>> {
    repeat(0.., seq!(parse_usize, _: space1, dec_uint, _: newline)).parse_next(str)
}

#[aoc(2024, 1)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let l = self
            .line
            .iter()
            .map(|p| p.0)
            .sorted()
            .collect::<Vec<usize>>();
        let r = self
            .line
            .iter()
            .map(|p| p.1)
            .sorted()
            .collect::<Vec<usize>>();

        l.iter()
            .zip(r.iter())
            .collect::<Vec<_>>()
            .iter()
            .map(|(a, b)| a.abs_diff(**b))
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut hash: HashMap<usize, usize> = HashMap::new();
        for i in self.line.iter().map(|p| p.1) {
            *hash.entry(i).or_default() += 1;
        }
        self.line
            .iter()
            .map(|p| p.0)
            .map(|i| i * hash.get(&i).unwrap_or(&0))
            .sum::<usize>()
    }
}
