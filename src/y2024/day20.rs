//! <https://adventofcode.com/2024/day/20>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::*,
        parser::parse_usize,
        rect::Rect,
    },
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap},
        hash::BuildHasherDefault,
        usize,
    },
    winnow::{
        ascii::newline,
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
enum Kind {
    #[default]
    Empty,
    Wall,
    End,
    Start,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    mapping: Rect<bool>,
    dist: Rect<usize>,
    size: Vec2,
    pos: Vec2,
    dir: Direction,
    goal: Vec2,
}

fn parse_line(s: &mut &str) -> PResult<Vec<Kind>> {
    repeat(1.., one_of(&['#', '.', 'E', 'S']))
        .map(|v: String| {
            v.chars()
                .map(|c| match c {
                    '.' => Kind::Empty,
                    '#' => Kind::Wall,
                    'E' => Kind::End,
                    'S' => Kind::Start,
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>()
        })
        .parse_next(s)
}

fn parse(s: &mut &str) -> PResult<Vec<Vec<Kind>>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc(2024, 20)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let line = parse(&mut input.as_str())?;
        let Puzzle {
            mapping,
            size,
            pos,
            dir,
            goal,
            ..
        } = self;
        *size = (line.len() as isize, line[0].len() as isize);
        for (i, l) in line.iter().enumerate() {
            for (j, k) in l.iter().enumerate() {
                match k {
                    Kind::Start => {
                        *pos = (i as isize, j as isize);
                    }
                    Kind::End => {
                        *goal = (i as isize, j as isize);
                    }
                    _ => (),
                }
            }
        }
        *mapping = Rect::from_vec(line).map(|c| *c != Kind::Wall);
        *dir = Direction::EAST;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        self.dist = Rect::new(self.size, usize::MAX);
        let mut pos: Vec2 = self.pos;
        let mut dist: usize = 0;
        self.dist[pos] = dist;
        'next: while pos != self.goal {
            for q in pos.neighbors4((0, 0), self.size).iter() {
                if self.mapping[q] && dist < self.dist[q] {
                    dist += 1;
                    pos = *q;
                    self.dist[q] = dist;
                    continue 'next;
                }
            }
        }
        self.dist[self.goal] = dist;
    }
    fn part1(&mut self) -> Self::Output1 {
        const POS: [Vec2; 4] = [
            (-2, 0),
            // (-1, -1),
            // (-1, 0),
            // (-1, 1),
            (0, -2),
            // (0, -1),
            // (0, 1),
            (0, 2),
            // (1, -1),
            // (1, 0),
            // (1, 1),
            (2, 0),
        ];
        const THRESHOLD: usize = 100;
        self.mapping
            .iter()
            .filter(|(_, b)| **b)
            .map(|(p, v)| {
                POS.iter()
                    .map(|off| {
                        if let Some(q) = p.add(off).included((0, 0), &self.size) {
                            if self.dist[q] != usize::MAX
                                && self.dist[p] + 2 + THRESHOLD <= self.dist[q]
                            {
                                1
                            } else {
                                0
                            }
                        } else {
                            0
                        }
                    })
                    .sum::<usize>()
            })
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
