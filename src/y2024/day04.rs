//! <https://adventofcode.com/2024/day/4>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    rayon::prelude::*,
    serde::Serialize,
    std::collections::HashMap,
    winnow::{
        ascii::{alpha1, newline},
        combinator::separated,
        PResult, Parser,
    },
};

#[derive(Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
    hash: HashMap<(isize, isize), char>,
}

const STENCILS: [[(isize, isize); 4]; 8] = [
    [(0, 0), (1, 0), (2, 0), (3, 0)],
    [(0, 0), (-1, 0), (-2, 0), (-3, 0)],
    [(0, 0), (0, 1), (0, 2), (0, 3)],
    [(0, 0), (0, -1), (0, -2), (0, -3)],
    [(0, 0), (1, 1), (2, 2), (3, 3)],
    [(0, 0), (-1, -1), (-2, -2), (-3, -3)],
    [(0, 0), (1, -1), (2, -2), (3, -3)],
    [(0, 0), (-1, 1), (-2, 2), (-3, 3)],
];

fn parse(str: &mut &str) -> PResult<Vec<Vec<char>>> {
    let v: Vec<&str> = separated(1.., alpha1, newline).parse_next(str)?;
    Ok(v.iter()
        .map(|v| v.chars().collect::<Vec<char>>())
        .collect::<Vec<_>>())
}

#[aoc(2024, 4)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(&mut input.as_str())?;
        Ok("".to_string())
    }
    fn end_of_data(&mut self) {
        for (i, l) in self.line.iter().enumerate() {
            for (j, c) in l.iter().enumerate() {
                self.hash.insert((i as isize, j as isize), *c);
            }
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        self.hash
            .par_iter()
            .filter(|(_, c)| **c == 'X')
            .map(|(p, _)| {
                STENCILS
                    .iter()
                    .filter(|offets| {
                        ['X', 'M', 'A', 'S']
                            .iter()
                            .zip(offets.iter())
                            .all(|(d, x)| self.hash.get(&(p.0 + x.0, p.1 + x.1)) == Some(d))
                    })
                    .count()
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output1 {
        self.hash
            .par_iter()
            .filter(|(_, c)| **c == 'A')
            .filter(|(p, _)|
                    {
                        let a = self.hash.get(&(p.0 - 1, p.1 - 1)).unwrap_or(&'P');
                        let b = self.hash.get(&(p.0 + 1, p.1 + 1)).unwrap_or(&'P');
                        *a.min(b) == 'M' && *a.max(b) == 'S'
                    }
                    && {
                        let a = self.hash.get(&(p.0 - 1, p.1 + 1)).unwrap_or(&'P');
                        let b = self.hash.get(&(p.0 + 1, p.1 - 1)).unwrap_or(&'P');
                        *a.min(b) == 'M' && *a.max(b) == 'S'
                    }
            )
            .count()
    }
}
