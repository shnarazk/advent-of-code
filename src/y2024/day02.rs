//! <https://adventofcode.com/2024/day/2>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser::parse_usize,
    },
    serde::Serialize,
    winnow::{
        ModalResult, Parser,
        ascii::{newline, space1},
        combinator::{repeat, separated, terminated},
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

fn parse_line(str: &mut &str) -> ModalResult<Vec<usize>> {
    separated(1.., parse_usize, space1).parse_next(str)
}

fn satisfy(lvls: &[usize]) -> bool {
    (lvls.windows(2).all(|v| v[0] < v[1]) || lvls.windows(2).all(|v| v[0] > v[1]))
        && lvls
            .windows(2)
            .all(|v| (1..=3).contains(&v[0].abs_diff(v[1])))
}

#[aoc(2024, 2)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = repeat(0.., terminated(parse_line, newline)).parse_next(&mut input)?;
        Ok(())
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
