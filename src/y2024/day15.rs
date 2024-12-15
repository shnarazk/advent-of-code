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
    fn as_char2(&self) -> (char, char, Option<char>) {
        match self {
            Kind::Empty => ('.', '.', None),
            Kind::Wall => ('#', '#', None),
            Kind::Box => ('[', ']', None),
            Kind::Robot => ('@', '.', None),
            Kind::BoxH => ('.', '[', Some(']')),
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
    fn dump2(&self) {
        let mut s = String::new();
        for i in 0..self.mapping.size.0 {
            let mut follow: Option<char> = None;
            for j in 0..self.mapping.size.1 {
                if self.pos == (i, j) {
                    if self.pos_half {
                        s.push(follow.map_or('.', |f| f));
                        s.push(self.dir.as_char());
                        follow = None;
                    } else if self.mapping[(i, j)] == Kind::BoxH {
                        let (_, b, f) = Kind::BoxH.as_char2();
                        s.push(self.dir.as_char());
                        s.push(b);
                        follow = f;
                    } else {
                        s.push(self.dir.as_char());
                        s.push('.');
                        follow = None;
                    }
                } else {
                    let (a, b, f) = self.mapping[(i, j)].as_char2();
                    s.push(follow.map_or(a, |p| p));
                    s.push(b);
                    follow = f;
                }
            }
            s.push('\n');
        }
        // progress_picture!(s);
        println!("{s}");
    }
}

impl Puzzle {
    fn unsupported_e(&self, pos: (Vec2, bool)) -> bool {
        if !pos.1 {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::Box => self.unsupported_e((pos.0.add(&(0, 1)), pos.1)),
                Kind::BoxH => true,
                Kind::Robot => unreachable!(),
            }
        } else {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::Box => unreachable!(),
                Kind::BoxH => self.unsupported_e((pos.0.add(&(0, 1)), pos.1)),
                Kind::Robot => unreachable!(),
            }
        }
    }
    fn unsupported_w(&self, pos: (Vec2, bool)) -> bool {
        if !pos.1 {
            match self.mapping[pos.0] {
                Kind::Empty => {
                    let w = pos.0.add(&(0, -1));
                    self.mapping[w] != Kind::BoxH || self.unsupported_w((w, false))
                }
                Kind::Wall => false,
                Kind::Box => self.unsupported_w((pos.0.add(&(0, -1)), true)),
                Kind::BoxH => {
                    let w = pos.0.add(&(0, -1));
                    self.mapping[w] != Kind::BoxH || self.unsupported_w((w, false))
                }
                Kind::Robot => unreachable!(),
            }
        } else {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::Box => self.unsupported_w((pos.0.add(&(0, -1)), pos.1)),
                Kind::BoxH => unreachable!(),
                Kind::Robot => unreachable!(),
            }
        }
    }
    fn unsupported_s(&self, pos: (Vec2, bool)) -> bool {
        if !pos.1 {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::BoxH => {
                    let w = pos.0.add(&(0, -1));
                    let s1 = pos.0.add(&(1, -1));
                    let s2 = pos.0.add(&(1, 0));
                    self.mapping[w] != Kind::BoxH
                        || (self.unsupported_s((s1, true)) && self.unsupported_s((s2, false)))
                }
                Kind::Box => {
                    let s = pos.0.add(&(1, 0));
                    self.unsupported_s((s, false)) && self.unsupported_s((s, true))
                }
                Kind::Robot => unreachable!(),
            }
        } else {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::BoxH => {
                    let s1 = pos.0.add(&(1, 0));
                    let s2 = pos.0.add(&(1, 1));
                    self.unsupported_s((s1, true)) && self.unsupported_s((s2, false))
                }
                Kind::Box => {
                    let s = pos.0.add(&(1, 0));
                    self.unsupported_s((s, false)) && self.unsupported_s((s, true))
                }
                Kind::Robot => unreachable!(),
            }
        }
    }
    fn unsupported_n(&self, pos: (Vec2, bool)) -> bool {
        if !pos.1 {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::BoxH => {
                    let w = pos.0.add(&(0, -1));
                    let n1 = pos.0.add(&(-1, -1));
                    let n2 = pos.0.add(&(-1, 0));
                    self.mapping[w] != Kind::BoxH
                        || (self.unsupported_n((n1, true)) && self.unsupported_n((n2, false)))
                }
                Kind::Box => {
                    let n = pos.0.add(&(-1, 0));
                    self.unsupported_n((n, false)) && self.unsupported_n((n, true))
                }
                Kind::Robot => unreachable!(),
            }
        } else {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::BoxH => {
                    let n1 = pos.0.add(&(-1, 0));
                    let n2 = pos.0.add(&(-1, 1));
                    self.unsupported_n((n1, true)) && self.unsupported_n((n2, false))
                }
                Kind::Box => {
                    let n = pos.0.add(&(-1, 0));
                    self.unsupported_n((n, false)) && self.unsupported_n((n, true))
                }
                Kind::Robot => unreachable!(),
            }
        }
    }
    fn unsupported(&mut self, pos: (Vec2, bool), dir: Direction) -> bool {
        match dir {
            Direction::NORTH => self.unsupported_n(pos),
            Direction::EAST => self.unsupported_e(pos),
            Direction::SOUTH => self.unsupported_s(pos),
            Direction::WEST => self.unsupported_w(pos),
        }
    }
    fn shift_e(&mut self, pos: (Vec2, bool)) -> bool {
        if !pos.1 {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::Box => {
                    self.shift_e((pos.0.add(&(0, 1)), pos.1));
                    self.mapping[pos.0] = Kind::BoxH;
                    true
                }
                Kind::BoxH => true,
                Kind::Robot => unreachable!(),
            }
        } else {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::Box => unreachable!(),
                Kind::BoxH => {
                    let e = pos.0.add(&(0, 1));
                    self.shift_e((e, pos.1));
                    self.mapping[pos.0] = Kind::Empty;
                    self.mapping[e] = Kind::Box;
                    true
                }
                Kind::Robot => unreachable!(),
            }
        }
    }
    fn shift_w(&mut self, pos: (Vec2, bool)) -> bool {
        if !pos.1 {
            match self.mapping[pos.0] {
                Kind::Empty => {
                    let w = pos.0.add(&(0, -1));
                    // self.mapping[w] != Kind::BoxH || self.unsupported_w((w, false))
                    if self.mapping[w] == Kind::BoxH {
                        self.shift_w((w, false));
                        self.mapping[w] = Kind::Box;
                    }
                    true
                }
                Kind::Wall => false,
                Kind::Box => {
                    let w = pos.0.add(&(0, -1));
                    self.shift_w((w, true));
                    self.mapping[pos.0] = Kind::Empty;
                    self.mapping[w] = Kind::BoxH;
                    true
                }
                Kind::BoxH => {
                    let w = pos.0.add(&(0, -1));
                    // self.mapping[w] != Kind::BoxH || self.unsupported_w((w, false))
                    if self.mapping[w] == Kind::BoxH {
                        self.shift_w((w, false));
                        self.mapping[w] = Kind::Box;
                    }
                    true
                }
                Kind::Robot => unreachable!(),
            }
        } else {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::Box => {
                    let w = pos.0.add(&(0, -1));
                    self.shift_w((w, pos.1));
                    self.mapping[pos.0] = Kind::Empty;
                    self.mapping[w] = Kind::BoxH;
                    true
                }
                Kind::BoxH => unreachable!(),
                Kind::Robot => unreachable!(),
            }
        }
    }
    fn shift_s(&mut self, pos: (Vec2, bool)) -> bool {
        if !pos.1 {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::BoxH => {
                    let w = pos.0.add(&(0, -1));
                    let s1 = pos.0.add(&(1, -1));
                    let s2 = pos.0.add(&(1, 0));
                    // self.mapping[w] != Kind::BoxH
                    //     || (self.shift_s((s1, true)) && self.shift_s((s2, false)))
                    if self.mapping[w] == Kind::BoxH {
                        self.shift_s((s1, true));
                        self.shift_s((s2, false));
                        self.mapping[w] = Kind::Empty;
                        self.mapping[s1] = Kind::BoxH;
                    }
                    true
                }
                Kind::Box => {
                    let s = pos.0.add(&(1, 0));
                    // self.shift_s((s, false)) && self.shift_s((s, true))
                    self.shift_s((s, false));
                    self.shift_s((s, true));
                    self.mapping[pos.0] = Kind::Empty;
                    self.mapping[s] = Kind::Box;
                    true
                }
                Kind::Robot => unreachable!(),
            }
        } else {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::BoxH => {
                    let s1 = pos.0.add(&(1, 0));
                    let s2 = pos.0.add(&(1, 1));
                    // self.shift_s((s1, true)) && self.shift_s((s2, false))
                    self.shift_s((s1, true));
                    self.shift_s((s2, false));
                    self.mapping[pos.0] = Kind::Empty;
                    self.mapping[s1] = Kind::BoxH;
                    true
                }
                Kind::Box => {
                    let s = pos.0.add(&(1, 0));
                    // self.shift_s((s1, true)) && self.shift_s((s2, false))
                    self.shift_s((s, false));
                    self.shift_s((s, true));
                    self.mapping[pos.0] = Kind::Empty;
                    self.mapping[s] = Kind::BoxH;
                    true
                }
                Kind::Robot => unreachable!(),
            }
        }
    }
    fn shift_n(&mut self, pos: (Vec2, bool)) -> bool {
        if !pos.1 {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::BoxH => {
                    let w = pos.0.add(&(0, -1));
                    let n1 = pos.0.add(&(-1, -1));
                    let n2 = pos.0.add(&(-1, 0));
                    // self.mapping[w] != Kind::BoxH
                    //     || (self.shift_n((s1, true)) && self.shift_n((s2, false)))
                    if self.mapping[w] == Kind::BoxH {
                        self.shift_n((n1, true));
                        self.shift_n((n2, false));
                        self.mapping[w] = Kind::Empty;
                        self.mapping[n1] = Kind::BoxH;
                    }
                    true
                }
                Kind::Box => {
                    let n = pos.0.add(&(-1, 0));
                    // self.shift_n((n, false)) && self.shift_n((n, true))
                    self.shift_n((n, false));
                    self.shift_n((n, true));
                    self.mapping[pos.0] = Kind::Empty;
                    self.mapping[n] = Kind::Box;
                    true
                }
                Kind::Robot => unreachable!(),
            }
        } else {
            match self.mapping[pos.0] {
                Kind::Empty => true,
                Kind::Wall => false,
                Kind::BoxH => {
                    let n1 = pos.0.add(&(-1, 0));
                    let n2 = pos.0.add(&(-1, 1));
                    // self.shift_n((n1, true)) && self.shift_n((n2, false))
                    self.shift_n((n1, true));
                    self.shift_n((n2, false));
                    self.mapping[pos.0] = Kind::Empty;
                    self.mapping[n1] = Kind::BoxH;
                    true
                }
                Kind::Box => {
                    let n = pos.0.add(&(-1, 0));
                    // self.shift_n((n1, true)) && self.shift_n((n2, false))
                    self.shift_n((n, false));
                    self.shift_n((n, true));
                    self.mapping[pos.0] = Kind::Empty;
                    self.mapping[n] = Kind::Box;
                    true
                }
                Kind::Robot => unreachable!(),
            }
        }
    }
    fn shift(&mut self, pos: (Vec2, bool), dir: Direction) -> bool {
        match dir {
            Direction::NORTH => self.shift_n(pos),
            Direction::EAST => self.shift_e(pos),
            Direction::SOUTH => self.shift_s(pos),
            Direction::WEST => self.shift_w(pos),
        }
    }
    fn press2(&mut self, t: usize) {
        self.dir = self.moves[t];
        let next = match (self.dir, self.pos_half) {
            (Direction::NORTH, b) => (self.pos.add(&(-1, 0)), b),
            (Direction::SOUTH, b) => (self.pos.add(&(1, 0)), b),
            (Direction::EAST, false) => (self.pos, true),
            (Direction::EAST, true) => (self.pos.add(&(0, 1)), false),
            (Direction::WEST, false) => (self.pos.add(&(0, -1)), true),
            (Direction::WEST, true) => (self.pos, false),
        };
        if self.unsupported(next, self.dir) {
            self.shift(next, self.dir);
            self.pos = next.0;
            self.pos_half = next.1;
        }
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
        self.dump2();
        for t in 0..self.moves.len().min(322) {
            self.press2(t);
            let time = t + 1;
            println!("{time}, Move {}:", self.dir.as_char());
            self.dump2();
        }
        // self.evaluate2()
        0
    }
}
