//! <https://adventofcode.com/2024/day/1>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    itertools::Itertools,
    serde::Serialize,
    std::collections::HashMap,
    winnow::{
        ascii::{dec_uint, newline, space1},
        combinator::{repeat, terminated},
        PResult, Parser,
    },
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<(u64, u64)>,
}

fn parse(str: &mut &str) -> PResult<Vec<(u64, u64)>> {
    repeat(
        0..,
        (terminated(dec_uint, space1), terminated(dec_uint, newline)),
    )
    .parse_next(str)
}

#[aoc(2024, 1)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(&mut input.as_str())?;
        Ok("".to_string())
    }
    fn part1(&mut self) -> Self::Output1 {
        let l = self.line.iter().map(|p| p.0).sorted().collect::<Vec<u64>>();
        let r = self.line.iter().map(|p| p.1).sorted().collect::<Vec<u64>>();

        l.iter()
            .zip(r.iter())
            .collect::<Vec<_>>()
            .iter()
            .map(|(a, b)| a.abs_diff(**b) as usize)
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut hash: HashMap<usize, usize> = HashMap::new();
        for i in self.line.iter().map(|p| p.1 as usize) {
            *hash.entry(i).or_default() += 1;
        }
        self.line
            .iter()
            .map(|p| p.0 as usize)
            .map(|i| i * hash.get(&i).unwrap_or(&0))
            .sum::<usize>()
    }
}
