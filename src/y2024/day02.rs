//! <https://adventofcode.com/2024/day/2>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    serde::Serialize,
    winnow::{
        ascii::{dec_uint, newline, space1},
        combinator::{repeat, separated, terminated},
        PResult, Parser,
    },
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<Vec<u64>>,
}

fn parse_line(str: &mut &str) -> PResult<Vec<u64>> {
    separated(1.., dec_uint::<&str, u64, _>, space1).parse_next(str)
}

fn satisfy(lvls: &[u64]) -> bool {
    (lvls.windows(2).all(|v| v[0] < v[1]) || lvls.windows(2).all(|v| v[0] > v[1]))
        && lvls
            .windows(2)
            .all(|v| (1..=3).contains(&v[0].abs_diff(v[1])))
}

#[aoc(2024, 2)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = repeat(0.., terminated(parse_line, newline)).parse_next(&mut input.as_str())?;
        Ok("".to_string())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().filter(|l| satisfy(l)).count()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .filter(|ls| {
                satisfy(ls)
                    || (0..ls.len()).any(|i| {
                        let mut levels = (*ls).clone();
                        levels.remove(i);
                        satisfy(&levels)
                    })
            })
            .count()
    }
}
