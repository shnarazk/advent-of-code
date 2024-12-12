//! <https://adventofcode.com/2024/day/12>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{GeometricMath, Vec2},
        parser,
        rect::Rect,
    },
    rayon::prelude::*,
    serde::Serialize,
    std::collections::{HashMap, VecDeque},
    winnow::{
        ascii::{alpha1, newline},
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    mapping: Rect<char>,
}
impl Puzzle {
    fn area_for(&self, pos: Vec2) -> usize {
        let Some(c) = self.mapping.get(&pos) else {
            return 0;
        };
        let mut count = 0;
        let mut r: Rect<Option<bool>> = self.mapping.map(|_| None);
        let mut to_visid: Vec<Vec2> = vec![pos];
        while let Some(p) = to_visid.pop() {
            if let Some(None) = r.get(&p) {
                if self.mapping[&p] == *c {
                    count += 1;
                    r[&p] = Some(true);
                    for q in p.neighbors4((0, 0), self.mapping.size()).iter() {
                        to_visid.push(*q);
                    }
                } else {
                    r[&p] = Some(false);
                }
            }
        }
        count
    }
}

fn parse<'a>(s: &'a mut &str) -> PResult<Vec<&'a str>> {
    separated(1.., alpha1, newline).parse_next(s)
}

#[aoc(2024, 12)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let s = &mut input.as_str();
        let v = parse(s)?;
        self.mapping = Rect::from_vec(
            v.iter()
                .map(|l| l.chars().collect::<Vec<char>>())
                .collect::<Vec<_>>(),
        );
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.mapping
            .iter()
            .map(|(pos, c)| {
                let a = pos
                    .neighbors4((-1, -1), self.mapping.size().add(&(1, 1)))
                    .iter()
                    .map(|q| (self.mapping.get(q) != Some(c)) as usize)
                    .sum::<usize>();
                let b = self.area_for(pos);
                println!("{pos:?}: {a}, {b} = {}", a * b);
                a * b
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.mapping.iter().map(|(pos, c)| 1).sum()
    }
}
