//! <https://adventofcode.com/2024/day/10>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::*,
        parser::parse_dec,
    },
    serde::Serialize,
    std::collections::{HashMap, HashSet},
    winnow::{
        ascii::newline,
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
    plane: HashMap<Vec2, usize>,
    heads: HashSet<Vec2>,
    size: Vec2,
}

impl Puzzle {
    fn aux1(&self, accum: &mut HashSet<Vec2>, from: Vec2, lvl: usize) {
        if lvl == 9 {
            accum.insert(from);
        } else {
            from.neighbors4((0, 0), self.size).iter().for_each(|p| {
                let l = *self.plane.get(p).unwrap();
                if lvl + 1 == l {
                    // println!("{p:?}: {l}");
                    self.aux1(accum, *p, l);
                }
            });
        }
    }
    fn count9(&self, from: Vec2) -> usize {
        let mut result: HashSet<Vec2> = HashSet::new();
        self.aux1(&mut result, from, 0);
        result.len()
    }
}

fn parse_line(s: &mut &str) -> PResult<Vec<usize>> {
    let (v, _) = repeat_till(1.., parse_dec, newline).parse_next(s)?;
    Ok(v)
}

fn parse(s: &mut &str) -> PResult<Vec<Vec<usize>>> {
    repeat(1.., parse_line).parse_next(s)
}

#[aoc(2024, 10)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let s = &mut input.as_str();
        self.line = parse(s)?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for (i, l) in self.line.iter().enumerate() {
            for (j, &n) in l.iter().enumerate() {
                self.plane.insert((i as isize, j as isize), n);
                if n == 0 {
                    self.heads.insert((i as isize, j as isize));
                }
            }
        }
        self.size.0 = self.line.len() as isize;
        self.size.1 = self.line[0].len() as isize;
        dbg!(&self.heads.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        self.heads.iter().map(|&h| self.count9(h)).sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
