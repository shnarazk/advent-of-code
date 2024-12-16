//! <https://adventofcode.com/2024/day/16>
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
        collections::{BinaryHeap, HashMap, HashSet},
        hash::BuildHasherDefault,
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

impl Kind {
    fn as_char(&self) -> char {
        match self {
            Kind::Empty => '.',
            Kind::Wall => '#',
            Kind::End => 'E',
            Kind::Start => 'S',
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    mapping: Rect<bool>,
    size: Vec2,
    pos: Vec2,
    dir: Direction,
    goal: Vec2,
}

impl Puzzle {
    fn path_cost(&self) -> usize {
        let mut best = usize::MAX;
        let mut visited: Rect<Option<usize>> = self.mapping.map(|_| None);
        let mut to_visit: BinaryHeap<(usize, Vec2, Direction)> = BinaryHeap::new();
        to_visit.push((0, self.pos, self.dir));
        while let Some((cost, pos, dir)) = to_visit.pop() {
            if pos == self.goal {
                if cost < best {
                    best = cost;
                }
                continue;
            }
            if best < cost || visited[pos].map_or(false, |c| c < cost) {
                continue;
            }
            visited[pos] = Some(cost);
            for d in DIRECTIONS.iter() {
                if let Some(q) = pos.add(&d.as_vec2()).included((0, 0), &self.size) {
                    if self.mapping[q] {
                        let c = cost + if dir == *d { 1 } else { 1001 };
                        to_visit.push((c, *q, *d));
                    }
                }
            }
        }
        best
    }
    fn a_best_path_map(&self) -> (usize, Vec<(Vec2, Direction)>, Rect<Option<usize>>) {
        type SEARCHSPACE = (usize, Vec<(Vec2, Direction)>);
        let mut best = usize::MAX;
        let mut best_path: Vec<(Vec2, Direction)> = Vec::new();
        let mut best_map: Rect<Option<usize>> = self.mapping.map(|_| None);
        let mut visited: Rect<Option<usize>> = self.mapping.map(|_| None);
        let mut to_visit: BinaryHeap<SEARCHSPACE> = BinaryHeap::new();
        to_visit.push((0, vec![(self.pos, self.dir)]));
        while let Some((cost, path)) = to_visit.pop() {
            let (pos, dir) = *path.last().unwrap();
            if pos == self.goal {
                if cost < best {
                    visited[self.goal] = Some(cost);
                    best = cost;
                    best_map.clear(None);
                    for p in path.iter() {
                        best_map[p.0] = visited[p.0];
                    }
                    best_path = path;
                }
                continue;
            }
            if best < cost || visited[pos].map_or(false, |c| c < cost) {
                continue;
            }
            visited[pos] = Some(cost);
            for d in DIRECTIONS.iter() {
                if let Some(q) = pos.add(&d.as_vec2()).included((0, 0), &self.size) {
                    if self.mapping[q] {
                        let c = cost + if dir == *d { 1 } else { 1001 };
                        let mut new_path = path.clone();
                        new_path.push((*q, *d));
                        to_visit.push((c, new_path));
                    }
                }
            }
        }
        (best, best_path, best_map)
    }
    fn best_tiles(
        &self,
        threshold: usize,
        cands: &[(Vec2, Direction)],
        best_map: &Rect<Option<usize>>,
    ) -> usize {
        type SEARCHSPACE = (usize, Vec<(Vec2, Direction)>);
        let mut tiles: HashSet<Vec2> = HashSet::new();
        let mut visited: HashMap<(Vec2, Direction), usize> = HashMap::new();
        let mut to_visit: BinaryHeap<SEARCHSPACE> = BinaryHeap::new();

        for &(pos, dir) in cands.iter() {
            let cost = best_map[pos].unwrap();
            tiles.insert(pos);
            for &d in DIRECTIONS.iter() {
                if let Some(q) = pos.add(&d.as_vec2()).included((0, 0), &self.size) {
                    if self.mapping[q] {
                        let c = cost + if dir == d { 1 } else { 1001 };
                        to_visit.push((c, vec![(*q, d)]));
                    }
                }
            }
        }

        // to_visit.push((0, vec![self.pos], self.dir));
        while let Some((cost, path)) = to_visit.pop() {
            let (pos, dir) = *path.last().unwrap();
            if let Some(c) = best_map[pos] {
                if c == cost {
                    for p in path.iter() {
                        tiles.insert(p.0);
                    }
                    continue;
                }
            }
            if threshold < cost || visited.get(&(pos, dir)).map_or(false, |c| *c < cost) {
                continue;
            }
            visited.insert((pos, dir), cost);
            for d in DIRECTIONS.iter() {
                if let Some(q) = pos.add(&d.as_vec2()).included((0, 0), &self.size) {
                    if self.mapping[q] {
                        let c = cost + if dir == *d { 1 } else { 1001 };
                        let mut new_path = path.clone();
                        new_path.push((*q, *d));
                        to_visit.push((c, new_path));
                    }
                }
            }
        }
        tiles.len()
    }
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

#[aoc(2024, 16)]
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
    fn part1(&mut self) -> Self::Output1 {
        self.path_cost()
    }
    fn part2(&mut self) -> Self::Output2 {
        let (threshold, cands, map) = self.a_best_path_map();
        self.best_tiles(threshold, &cands, &map)
    }
}
