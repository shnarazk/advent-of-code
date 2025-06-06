//! <https://adventofcode.com/2024/day/20>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::*,
        rect::Rect,
    },
    rayon::prelude::*,
    serde::Serialize,
    winnow::{
        ModalResult, Parser,
        ascii::newline,
        combinator::{repeat, separated},
        token::one_of,
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
    start: Vec2,
    goal: Vec2,
    threshold: usize,
}

fn parse_line(s: &mut &str) -> ModalResult<Vec<Kind>> {
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

fn parse(s: &mut &str) -> ModalResult<Vec<Vec<Kind>>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc(2024, 20)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        let line = parse(&mut input)?;
        let Puzzle {
            mapping,
            size,
            start,
            goal,
            ..
        } = self;
        *size = (line.len() as isize, line[0].len() as isize);
        for (i, l) in line.iter().enumerate() {
            for (j, k) in l.iter().enumerate() {
                match k {
                    Kind::Start => {
                        *start = (i as isize, j as isize);
                    }
                    Kind::End => {
                        *goal = (i as isize, j as isize);
                    }
                    _ => (),
                }
            }
        }
        *mapping = Rect::from_vec(line).map(|c| *c != Kind::Wall);
        self.dist = Rect::new(self.size, usize::MAX);
        let mut pos: Vec2 = self.start;
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
        self.threshold = self.get_config().alt.as_ref().map_or(100, |_| 64);
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        const POS: [Vec2; 4] = [(-2, 0), (0, -2), (0, 2), (2, 0)];
        self.mapping
            .iter()
            .filter(|(_, b)| **b)
            .map(|(p, _)| {
                POS.iter()
                    .map(|off| {
                        if let Some(q) = p.add(off).included((0, 0), self.size) {
                            if self.dist[q] != usize::MAX
                                && self.dist[p] + 2 + self.threshold <= self.dist[q]
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
        self.mapping
            .iter()
            .filter(|(_, b)| **b)
            .collect::<Vec<_>>()
            .par_iter()
            .map(|(p, _)| {
                self.mapping
                    .iter()
                    .filter(|(_, b)| **b)
                    .map(|(q, _)| {
                        let dist = p.manhattan_distance(q);
                        (1 < dist
                            && dist <= 20
                            && self.dist[p] != usize::MAX
                            && self.dist[q] != usize::MAX
                            && self.dist[p] < self.dist[q]
                            && (dist as usize) + self.threshold <= self.dist[q] - self.dist[p])
                            as usize
                    })
                    .sum::<usize>()
            })
            .sum::<usize>()
    }
}
