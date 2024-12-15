//! <https://adventofcode.com/2024/day/15>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::*,
        parser::parse_usize,
        progress_picture,
        rect::Rect,
    },
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    serde::Serialize,
    std::{collections::HashMap, fmt, fs::DirEntry, hash::BuildHasherDefault},
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
    Box,
    Robot,
    BoxH,
}

impl Kind {
    fn as_char(&self) -> char {
        match self {
            Kind::Empty => '.',
            Kind::Wall => '#',
            Kind::Box => 'O',
            Kind::Robot => '@',
            Kind::BoxH => '\\',
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    mapping: Rect<Kind>,
    moves: Vec<Direction>,
    next_move: usize,
    pos: Vec2,
    dir: Direction,
    pos_half: bool,
}

impl Puzzle {
    fn press(&mut self, t: usize) {
        self.dir = self.moves[t];
        let next = self.pos.add(&self.dir.as_vec2());
        let mut p = next;
        while self.mapping[p] == Kind::Box {
            p = p.add(&self.dir.as_vec2());
        }
        match self.mapping[p] {
            Kind::Empty => {
                self.mapping[p] = Kind::Box;
                self.mapping[next] = Kind::Empty;
                self.pos = next;
            }
            Kind::Wall => (),
            Kind::Box | Kind::Robot | Kind::BoxH => unreachable!(),
        }
    }
    fn evaluate1(&self) -> usize {
        self.mapping
            .iter()
            .map(|(p, c)| {
                if *c == Kind::Box {
                    (p.0 * 100 + p.1) as usize
                } else {
                    0
                }
            })
            .sum()
    }
    fn dump(&self) {
        let mut s = String::new();
        for i in 0..self.mapping.size.0 {
            for j in 0..self.mapping.size.1 {
                if self.pos == (i, j) {
                    s.push(self.dir.as_char());
                } else {
                    s.push(self.mapping[(i, j)].as_char());
                }
            }
            s.push('\n');
        }
        progress_picture!(s);
    }
}

impl Puzzle {
    fn horizontal_unsupported(&self, pos: (Vec2, bool), dir: Direction) -> bool {
        if pos.1 {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::Box => self.horizontal_unsupported((pos.0.add(&dir.as_vec2()), true), dir),
                Kind::BoxH => unreachable!(),
                Kind::Robot => unreachable!(),
            }
        } else {
            match self.mapping[pos.0] {
                Kind::Empty => unreachable!(),
                Kind::BoxH => {
                    self.mapping[pos.0.add(&dir.as_vec2())] != Kind::BoxH
                        || self.horizontal_unsupported((pos.0.add(&dir.as_vec2()), true), dir)
                }
                Kind::Wall => unreachable!(),
                Kind::Box => unreachable!(),
                Kind::Robot => unreachable!(),
            }
        }
    }
    // FIXME
    fn push_horizontal(&mut self, pos: (Vec2, bool), dir: Direction) {
        if pos.1 {
            if self.mapping[pos.0] == Kind::Box {
                let next = pos.0.add(&dir.as_vec2());
                self.push_horizontal((next, true), dir);
            }
            self.mapping[pos.0] = Kind::BoxH;
        } else {
            // if self.mapping[pos.0] == Kind::Empty {
            //     Kind::Empty => self.mapping[pos.0.add(&dir.as_vec2()))] != Kind::BoxH,
            // }
            //     Kind::Wall => unreachable!(),
            //     Kind::Box => unreachable!(),
            //     Kind::BoxH => unreachable!(),
            //     Kind::Robot => unreachable!(),
            // };
            ()
        };
    }
    fn vertical_unsupported(&mut self, pos: (Vec2, bool), dir: Direction) -> bool {
        match self.mapping[pos.0] {
            Kind::Empty => true,
            Kind::Wall => false,
            Kind::Box => {
                self.vertical_unsupported((pos.0.add(&dir.as_vec2()), false), dir)
                    && self.vertical_unsupported((pos.0.add(&dir.as_vec2()), true), dir)
            }
            Kind::BoxH => {
                if pos.1 {
                    self.vertical_unsupported((pos.0.add(&dir.as_vec2()), true), dir)
                        && self.vertical_unsupported(
                            (pos.0.add(&dir.as_vec2().add(&(0, 1))), false),
                            dir,
                        )
                } else {
                    true
                }
            }
            Kind::Robot => unreachable!(),
        }
    }
    // FIXME
    fn push_vertical(&mut self, pos: (Vec2, bool), dir: Direction) {
        match self.mapping[pos.0] {
            Kind::Empty => true,
            Kind::Wall => false,
            Kind::Box => {
                self.vertical_unsupported((pos.0.add(&dir.as_vec2()), false), dir)
                    && self.vertical_unsupported((pos.0.add(&dir.as_vec2()), true), dir)
            }
            Kind::BoxH => {
                if pos.1 {
                    self.vertical_unsupported((pos.0.add(&dir.as_vec2()), true), dir)
                        && self.vertical_unsupported(
                            (pos.0.add(&dir.as_vec2().add(&(0, 1))), false),
                            dir,
                        )
                } else {
                    true
                }
            }
            Kind::Robot => unreachable!(),
        };
    }
    fn press2(&mut self, t: usize) {
        self.dir = self.moves[t];
        if [Direction::EAST, Direction::WEST].contains(&self.dir) {
            let next = if self.pos_half {
                (self.pos.add(&self.dir.as_vec2()), false)
            } else {
                (self.pos, true)
            };
            if self.horizontal_unsupported(next, self.dir) {
                self.push_horizontal(next, self.dir);
                self.pos = next.0;
                self.pos_half = next.1;
            }
        } else {
            let next = (self.pos.add(&self.dir.as_vec2()), self.pos_half);
            if self.vertical_unsupported(next, self.dir) {
                self.push_vertical(next, self.dir);
                self.pos = next.0;
                self.pos_half = next.1;
            }
        };
    }
    fn evaluate2(&self) -> usize {
        self.mapping
            .iter()
            .map(|(p, c)| {
                if *c == Kind::Box {
                    (p.0 * 100 + p.1) as usize
                } else {
                    0
                }
            })
            .sum()
    }
}

fn parse_line(s: &mut &str) -> PResult<Vec<Kind>> {
    repeat(1.., one_of(&['#', '.', 'O', '@']))
        .map(|v: String| {
            v.chars()
                .map(|c| match c {
                    '.' => Kind::Empty,
                    '#' => Kind::Wall,
                    'O' => Kind::Box,
                    '@' => Kind::Robot,
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>()
        })
        .parse_next(s)
}

fn parse_maze(s: &mut &str) -> PResult<Vec<Vec<Kind>>> {
    separated(1.., parse_line, newline).parse_next(s)
}

fn parse_moves_line(s: &mut &str) -> PResult<Vec<Direction>> {
    repeat(1.., one_of(&['^', '>', 'v', '<']))
        .map(|v: String| {
            v.chars()
                .map(|c| match c {
                    '^' => Direction::NORTH,
                    '>' => Direction::EAST,
                    'v' => Direction::SOUTH,
                    '<' => Direction::WEST,
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>()
        })
        .parse_next(s)
}

fn parse_moves(s: &mut &str) -> PResult<Vec<Direction>> {
    separated(1.., parse_moves_line, newline)
        .map(|v: Vec<Vec<Direction>>| v.iter().flatten().cloned().collect::<Vec<_>>())
        .parse_next(s)
}

fn parse(s: &mut &str) -> PResult<(Vec<Vec<Kind>>, Vec<Direction>)> {
    seq!(parse_maze, _: (newline, newline), parse_moves).parse_next(s)
}

#[aoc(2024, 15)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let s = &mut input.as_str();
        let (maze, moves) = parse(s)?;
        self.mapping = Rect::from_vec(maze);
        self.moves = moves;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        let mut pos = (0, 0);
        for (p, k) in self.mapping.iter() {
            if *k == Kind::Robot {
                self.pos = p;
                pos = p;
            }
        }
        self.mapping[pos] = Kind::Empty;
        self.next_move = 0;
    }
    fn part1(&mut self) -> Self::Output1 {
        for t in 0..self.moves.len() {
            self.press(t);
        }
        self.dump();
        self.evaluate1()
    }
    fn part2(&mut self) -> Self::Output2 {
        for t in 0..self.moves.len() {
            self.press2(t);
        }
        self.dump();
        self.evaluate2()
    }
}
