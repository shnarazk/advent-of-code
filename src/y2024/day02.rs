//! <https://adventofcode.com/2024/day/2>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    serde::Serialize,
    winnow::{
        ascii::{dec_uint, newline, space1},
        combinator::repeat,
        multi::separated1,
        sequence::terminated,
        IResult, Parser,
    },
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<Vec<u64>>,
}

fn parse_line(str: &str) -> IResult<&str, Vec<u64>> {
    let (r, v): (&str, Vec<u64>) =
        separated1(dec_uint::<&str, u64, winnow::error::Error<&str>>, space1).parse_next(str)?;
    Ok((r, v))
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
        self.line = repeat(0.., terminated(parse_line, newline))
            .parse_next(input.as_str())?
            .1;
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
