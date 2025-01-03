//! <https://adventofcode.com/2021/day/13>
use crate::framework::{aoc, AdventOfCode, ParseError};

fn folding_x(vec: &[Vec<bool>], pos: usize) -> Vec<Vec<bool>> {
    let mut result: Vec<Vec<bool>> = Vec::new();
    for v in vec.iter() {
        result.push(
            v.iter()
                .enumerate()
                .take(pos)
                .map(|(i, b)| {
                    if let Some(c) = v.get(2 * pos - i) {
                        *b || *c
                    } else {
                        *b
                    }
                })
                .collect::<Vec<bool>>(),
        );
    }
    result
}

fn folding_y(vec: &[Vec<bool>], pos: usize) -> Vec<Vec<bool>> {
    let mut result: Vec<Vec<bool>> = Vec::new();
    for i in 0..pos {
        if let Some(w) = vec.get(pos - i + pos) {
            result.push(
                vec[i]
                    .iter()
                    .enumerate()
                    .map(|(i, b)| *b || w[i])
                    .collect::<Vec<bool>>(),
            );
        } else {
            result.push(vec[i].clone());
        }
    }
    result
}

fn print_grid(vec: &[Vec<bool>]) {
    for v in vec.iter() {
        for b in v.iter() {
            print!("{}", if *b { '#' } else { '.' });
        }
        println!();
    }
}

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
    grid: Vec<Vec<bool>>,
    folding: Vec<(bool, usize)>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ascii::newline,
            combinator::{alt, separated, seq},
            PResult, Parser,
        },
    };

    fn parse_dot(s: &mut &str) -> PResult<(usize, usize)> {
        seq!(parse_usize, _: ",", parse_usize)
            .map(|(x, y)| (y, x))
            .parse_next(s)
    }

    fn parse_dots(s: &mut &str) -> PResult<Vec<(usize, usize)>> {
        separated(1.., parse_dot, newline).parse_next(s)
    }

    fn parse_folding(s: &mut &str) -> PResult<(bool, usize)> {
        seq!(_: "fold along ", alt(("x", "y")), _: "=", parse_usize)
            .map(|(s, n)| (s == "x", n))
            .parse_next(s)
    }

    fn parse_foldings(s: &mut &str) -> PResult<Vec<(bool, usize)>> {
        separated(1.., parse_folding, newline).parse_next(s)
    }

    #[allow(clippy::type_complexity)]
    pub fn parse(s: &mut &str) -> PResult<(Vec<(usize, usize)>, Vec<(bool, usize)>)> {
        seq!(parse_dots, _: (newline, newline), parse_foldings).parse_next(s)
    }
}

#[aoc(2021, 13)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let (dots, foldings) = parser::parse(&mut input.as_str())?;
        self.line = dots;
        self.folding = foldings;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        let height = self.line.iter().map(|(y, _)| y).max().unwrap() + 1;
        let width = self.line.iter().map(|(_, x)| x).max().unwrap() + 1;
        self.grid = Vec::new();
        self.grid.resize(height, Vec::new());
        for v in self.grid.iter_mut() {
            v.resize(width, false);
        }
        for (j, i) in self.line.iter() {
            self.grid[*j][*i] = true;
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut r = self.grid.clone();
        for (axis_is_x, pos) in self.folding.iter().take(1) {
            if *axis_is_x {
                r = folding_x(&r, *pos);
                // print_grid(&r);
            } else {
                r = folding_y(&r, *pos);
                // print_grid(&r);
            }
        }
        r.iter().map(|v| v.iter().filter(|b| **b).count()).sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut r = self.grid.clone();
        for (axis_is_x, pos) in self.folding.iter() {
            if *axis_is_x {
                r = folding_x(&r, *pos);
            } else {
                r = folding_y(&r, *pos);
            }
        }
        print_grid(&r);
        0
    }
}
