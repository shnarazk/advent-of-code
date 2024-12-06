//! <https://adventofcode.com/2024/day/6>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::*,
    },
    serde::Serialize,
    std::collections::HashSet,
    winnow::{
        ascii::{dec_uint, newline},
        combinator::{repeat, repeat_till, separated},
        token::{literal, one_of},
        PResult, Parser,
    },
};

#[derive(Debug, Eq, Hash, PartialEq, Serialize)]
enum Kind {
    Empty,
    Obst,
    Guard(Direction),
}

fn kind_from(c: &char) -> Kind {
    match *c {
        '.' => Kind::Empty,
        '#' => Kind::Obst,
        '^' => Kind::Guard(Direction::NORTH),
        'v' => Kind::Guard(Direction::SOUTH),
        '>' => Kind::Guard(Direction::EAST),
        '<' => Kind::Guard(Direction::WEST),
        _ => unreachable!(),
    }
}

#[derive(Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    mapping: Vec<Vec<char>>,
    hash: HashSet<(isize, isize)>,
    guard: (Vec2, Direction),
    size: (isize, isize),
}

impl Puzzle {
    fn next_pos(&mut self) -> Option<Vec2> {
        let p = self.guard.0.add(&self.guard.1.as_vec2());
        if (0..self.size.0).contains(&p.0) && (0..self.size.1).contains(&p.1) {
            Some(p)
        } else {
            None
        }
    }
    fn turn(&mut self) {
        self.guard.1 = self.guard.1.turn_right();
    }
}

fn parse_line(input: &mut &str) -> PResult<Vec<char>> {
    let v = repeat(1.., one_of(['.', '#', '<', '^', '>', 'v'])).parse_next(input)?;
    Ok(v)
}

fn parse(input: &mut &str) -> PResult<Vec<Vec<char>>> {
    separated(1.., parse_line, newline).parse_next(input)
}

#[aoc(2024, 6)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let str = &mut input.as_str();
        self.mapping = parse(str)?;
        Ok("".to_string())
    }
    fn end_of_data(&mut self) {
        for (i, l) in self.mapping.iter().enumerate() {
            self.size.0 = i as isize + 1;
            for (j, c) in l.iter().enumerate() {
                let pos = (i as isize, j as isize);
                match kind_from(c) {
                    Kind::Guard(d) => {
                        self.guard = (pos, d);
                    }
                    Kind::Obst => {
                        self.hash.insert(pos);
                    }
                    _ => (),
                }
                self.size.1 = j as isize + 1;
            }
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut trail: HashSet<Vec2> = HashSet::new();
        let mut pos = Some(self.guard.0);
        while let Some(p) = pos {
            self.guard.0 = p;
            trail.insert(self.guard.0);
            pos = self.next_pos();
            if let Some(p) = pos {
                if self.hash.contains(&p) {
                    self.turn();
                    pos = self.next_pos();
                    if let Some(p) = pos {
                        if self.hash.contains(&p) {
                            self.turn();
                            pos = self.next_pos();
                        }
                    }
                }
            }
        }
        trail.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
