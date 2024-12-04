//! <https://adventofcode.com/2024/day/4>
// #![allow(dead_code)]
// #![allow(unused_imports)]
// #![allow(unused_variables)]
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    nom::{
        character::complete::{alpha1, newline},
        multi::separated_list1,
        IResult,
    },
    serde::Serialize,
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
    hash: HashMap<(isize, isize), char>,
    size: (usize, usize),
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

fn parse(str: &str) -> IResult<&str, Vec<Vec<char>>> {
    let (r, v) = separated_list1(newline, alpha1)(str)?;
    Ok((
        r,
        v.iter()
            .map(|v| v.chars().collect::<Vec<char>>())
            .collect::<Vec<_>>(),
    ))
}

#[aoc(2024, 4)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(input.as_str())?.1;
        Ok("".to_string())
    }
    fn end_of_data(&mut self) {
        for (i, l) in self.line.iter().enumerate() {
            for (j, c) in l.iter().enumerate() {
                self.hash.insert((i as isize, j as isize), *c);
                self.size.1 = j + 1;
            }
            self.size.0 = i + 1;
        }
        dbg!(&self.size);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.hash
            .iter()
            .map(|(p, _)| {
                STENCILS
                    .iter()
                    .filter(|offets| {
                        ['X', 'M', 'A', 'S']
                            .iter()
                            .zip(offets.iter())
                            .all(|(c, x)| {
                                let q = (p.0 + x.0, p.1 + x.1);
                                self.hash.get(&q) == Some(c)
                            })
                    })
                    .count()
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
