//! <https://adventofcode.com/2024/day/8>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::*,
        parser::parse_usize,
    },
    serde::Serialize,
    std::collections::{HashMap, HashSet},
    winnow::{
        ascii::newline,
        combinator::{repeat, repeat_till, separated, terminated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Debug, Eq, Hash, PartialEq, Serialize)]
enum Kind {
    Empty,
    Antinode,
}

fn kind_from(c: &char) -> Kind {
    match *c {
        '.' => Kind::Empty,
        'a' => Kind::Antinode,
        _ => unreachable!(),
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    plane: Vec<Vec<char>>,
    antenna: Vec<(Vec2, char)>,
    antinode: HashSet<Vec2>,
    size: Vec2,
    // trail: HashMap<Vec2, Option<(Vec2, Direction)>>,
}

impl Puzzle {
    fn check_pos(&self, p: Vec2) -> Option<Vec2> {
        ((0..self.size.0).contains(&p.0) && (0..self.size.1).contains(&p.1)).then_some(p)
    }
}

fn parse_line(input: &mut &str) -> PResult<Vec<char>> {
    let v = repeat(1.., one_of(['.', '#', 'a'])).parse_next(input)?;
    Ok(v)
}

fn parse(input: &mut &str) -> PResult<Vec<Vec<char>>> {
    separated(1.., parse_line, newline).parse_next(input)
}

#[aoc(2024, 8)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.plane = input
            .split('\n')
            .filter(|l| !l.is_empty())
            .map(|l| l.chars().collect::<Vec<char>>())
            .collect::<Vec<_>>();
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for (i, l) in self.plane.iter().enumerate() {
            for (j, c) in l.iter().enumerate() {
                if *c != '.' {
                    self.antenna.push(((i as isize, j as isize), *c));
                }
                self.size.1 = j as isize + 1;
            }
            self.size.0 = i as isize + 1;
        }
        dbg!(self.antenna.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        for (i, (p, f1)) in self.antenna.iter().enumerate() {
            for (j, (q, f2)) in self.antenna.iter().enumerate() {
                if i < j && f1 == f2 {
                    let d = q.sub(&p);
                    if let Some(a) = self.check_pos(p.sub(&d)) {
                        self.antinode.insert(a);
                    }
                    if let Some(b) = self.check_pos(q.add(&d)) {
                        self.antinode.insert(b);
                    }
                }
            }
        }
        self.antinode.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        for (i, (p, f1)) in self.antenna.iter().enumerate() {
            for (j, (q, f2)) in self.antenna.iter().enumerate() {
                if i < j && f1 == f2 {
                    let d0 = q.sub(&p);
                    {
                        let mut d = (0, 0);
                        for i in 1.. {
                            if let Some(a) = self.check_pos(p.sub(&d)) {
                                self.antinode.insert(a);
                                d = d.add(&d0);
                            } else {
                                break;
                            }
                        }
                    }
                    {
                        let mut d = (0, 0);
                        for i in 1.. {
                            if let Some(b) = self.check_pos(q.add(&d)) {
                                self.antinode.insert(b);
                                d = d.add(&d0);
                            } else {
                                break;
                            }
                        }
                    }
                }
            }
        }
        self.antinode.len()
    }
}
