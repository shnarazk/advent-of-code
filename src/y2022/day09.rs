//! <https://adventofcode.com/2022/day/9>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser::parse_usize,
    },
    std::collections::HashSet,
    winnow::{
        ModalResult, Parser,
        ascii::newline,
        combinator::{separated, seq},
        token::one_of,
    },
};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Dir {
    R(usize),
    U(usize),
    L(usize),
    D(usize),
}

impl Dir {
    fn steps(&self) -> usize {
        match self {
            Dir::R(n) => *n,
            Dir::U(n) => *n,
            Dir::L(n) => *n,
            Dir::D(n) => *n,
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Dir>,
    head: (isize, isize),
    tail: (isize, isize),
    trail: HashSet<(isize, isize)>,
    knots: Vec<(isize, isize)>,
}

fn parse_line(s: &mut &str) -> ModalResult<Dir> {
    seq!(one_of(&['R', 'U', 'L', 'D']), _: " ", parse_usize)
        .map(|(c, n)| match c {
            'R' => Dir::R(n),
            'U' => Dir::U(n),
            'L' => Dir::L(n),
            'D' => Dir::D(n),
            _ => unreachable!(),
        })
        .parse_next(s)
}

fn parse(s: &mut &str) -> ModalResult<Vec<Dir>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc(2022, 9)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        for dir in self.line.clone().iter() {
            self.move_head(dir);
        }
        self.trail.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.knots = vec![(0, 0); 10];
        for dir in self.line.clone().iter() {
            self.move_head_part2(dir);
        }
        self.trail.len()
    }
}

impl Puzzle {
    fn move_head(&mut self, dir: &Dir) {
        for _ in 0..dir.steps() {
            let v = match dir {
                Dir::R(_) => (0, 1),
                Dir::U(_) => (-1, 0),
                Dir::L(_) => (0, -1),
                Dir::D(_) => (1, 0),
            };
            self.head.0 += v.0 as isize;
            self.head.1 += v.1 as isize;
            let dy = self.head.0 - self.tail.0;
            let dx = self.head.1 - self.tail.1;
            if 1 < dy.abs() * dx.abs() {
                self.tail.0 += dy / dy.abs();
                self.tail.1 += dx / dx.abs();
            } else if 1 < dy.abs() {
                self.tail.0 += dy / dy.abs();
            } else if 1 < dx.abs() {
                self.tail.1 += dx / dx.abs();
            }
            self.trail.insert(self.tail);
        }
        // dbg!(self.trail.len());
    }
    fn move_head_part2(&mut self, dir: &Dir) {
        for _ in 0..dir.steps() {
            let v = match dir {
                Dir::R(_) => (0, 1),
                Dir::U(_) => (-1, 0),
                Dir::L(_) => (0, -1),
                Dir::D(_) => (1, 0),
            };
            self.knots[0].0 += v.0 as isize;
            self.knots[0].1 += v.1 as isize;
            for i in 1..self.knots.len() {
                let dy = self.knots[i - 1].0 - self.knots[i].0;
                let dx = self.knots[i - 1].1 - self.knots[i].1;
                if 1 < dy.abs() * dx.abs() {
                    self.knots[i].0 += dy / dy.abs();
                    self.knots[i].1 += dx / dx.abs();
                } else if 1 < dy.abs() {
                    self.knots[i].0 += dy / dy.abs();
                } else if 1 < dx.abs() {
                    self.knots[i].1 += dx / dx.abs();
                }
            }
            self.trail.insert(*self.knots.last().unwrap());
        }
    }
}
