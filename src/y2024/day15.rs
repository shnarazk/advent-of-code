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
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_char())
    }
}

impl Kind {
    fn as_char(&self) -> char {
        match self {
            Kind::Empty => '.',
            Kind::Wall => '#',
            Kind::Box => 'O',
            Kind::Robot => '@',
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
            Kind::Box | Kind::Robot => unreachable!(),
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
        // let mut ret: FxHashMap<usize, usize> = HashMap::<usize, usize, BuildHasherDefault<FxHasher>>::default();
        for t in 0..self.moves.len() {
            self.press(t);
        }
        self.dump();
        self.evaluate1()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
