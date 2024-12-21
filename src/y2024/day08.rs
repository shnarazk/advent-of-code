//! <https://adventofcode.com/2024/day/8>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::*,
    },
    serde::Serialize,
    std::collections::HashSet,
};

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    plane: Vec<Vec<char>>,
    antenna: Vec<(Vec2, char)>,
    antinode: HashSet<Vec2>,
    size: Vec2,
}

impl Puzzle {
    fn check_pos(&self, p: Vec2) -> Option<Vec2> {
        ((0..self.size.0).contains(&p.0) && (0..self.size.1).contains(&p.1)).then_some(p)
    }
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
            for (j, &c) in l.iter().enumerate() {
                if c != '.' {
                    self.antenna.push(((i as isize, j as isize), c));
                }
            }
        }
        self.size = (self.plane.len() as isize, self.plane[0].len() as isize);
    }
    fn part1(&mut self) -> Self::Output1 {
        for (i, (p, f1)) in self.antenna.iter().enumerate() {
            for (j, (q, f2)) in self.antenna.iter().enumerate() {
                if i < j && f1 == f2 {
                    let d = q.sub(p);
                    if let Some(a) = self.check_pos(p.sub(d)) {
                        self.antinode.insert(a);
                    }
                    if let Some(b) = self.check_pos(q.add(d)) {
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
                    let d0 = q.sub(p);
                    let mut d = (0, 0);
                    while let Some(a) = self.check_pos(p.sub(d)) {
                        self.antinode.insert(a);
                        d = d.add(d0);
                    }
                    d = (0, 0);
                    while let Some(a) = self.check_pos(q.add(d)) {
                        self.antinode.insert(a);
                        d = d.add(d0);
                    }
                }
            }
        }
        self.antinode.len()
    }
}
