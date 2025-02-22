//! <https://adventofcode.com/2024/day/16>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::*,
        rect::Rect,
    },
    rustc_data_structures::fx::{FxHashMap, FxHashSet, FxHasher},
    serde::Serialize,
    std::{
        cmp::{Ordering, Reverse},
        collections::{BinaryHeap, HashMap, HashSet},
        hash::BuildHasherDefault,
    },
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
    size: Vec2,
    pos: Vec2,
    dir: Direction,
    goal: Vec2,
}

type SearchPoint = (Vec2, Direction);

fn count_points(
    visited: &FxHashMap<SearchPoint, (usize, FxHashSet<SearchPoint>)>,
    start: Vec2,
) -> usize {
    let mut tiles: FxHashSet<SearchPoint> = HashSet::<_, BuildHasherDefault<FxHasher>>::default();
    tiles.insert((start, Direction::NORTH));
    let root = DIRECTIONS.iter().map(|d| (start, *d)).fold(
        (
            usize::MAX,
            HashSet::<SearchPoint, BuildHasherDefault<FxHasher>>::default(),
        ),
        |accum, goal| {
            if let Some(pre) = visited.get(&goal) {
                match pre.0.cmp(&accum.0) {
                    Ordering::Less => (pre.0, pre.1.clone()),
                    Ordering::Equal => (
                        accum.0,
                        accum
                            .1
                            .union(&pre.1)
                            .cloned()
                            .collect::<HashSet<_, BuildHasherDefault<FxHasher>>>(),
                    ),
                    Ordering::Greater => accum,
                }
            } else {
                accum
            }
        },
    );
    let mut to_visit: Vec<(Vec2, Direction)> = root.1.iter().cloned().collect::<Vec<_>>();
    while let Some(p) = to_visit.pop() {
        if tiles.contains(&p) {
            continue;
        }
        tiles.insert(p);
        for q in visited.get(&p).unwrap().1.iter() {
            to_visit.push(*q);
        }
    }
    tiles.iter().map(|(p, _)| *p).collect::<HashSet<_>>().len()
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

#[aoc(2024, 16)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        let line = parse(&mut input)?;
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
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut best = usize::MAX;
        let mut visited: Rect<Option<usize>> = self.mapping.map(|_| None);
        let mut to_visit: BinaryHeap<Reverse<(usize, Vec2, Direction)>> = BinaryHeap::new();
        to_visit.push(Reverse((0, self.pos, self.dir)));
        while let Some(Reverse((cost, pos, dir))) = to_visit.pop() {
            if pos == self.goal {
                if cost < best {
                    best = cost;
                }
                continue;
            }
            if best < cost || visited[pos].is_some_and(|c| c < cost) {
                continue;
            }
            visited[pos] = Some(cost);
            for d in DIRECTIONS.iter() {
                if let Some(q) = pos.add(d.as_vec2()).included((0, 0), self.size) {
                    if self.mapping[q] {
                        let c = cost + if dir == *d { 1 } else { 1001 };
                        to_visit.push(Reverse((c, *q, *d)));
                    }
                }
            }
        }
        best
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut best = usize::MAX;
        let mut visited: FxHashMap<SearchPoint, (usize, FxHashSet<SearchPoint>)> =
            HashMap::<_, _, BuildHasherDefault<FxHasher>>::default();
        let mut to_visit: BinaryHeap<Reverse<(usize, (SearchPoint, SearchPoint))>> =
            BinaryHeap::new();
        to_visit.push(Reverse((0, ((self.pos, self.dir), (self.pos, self.dir)))));
        while let Some(Reverse((cost, (p @ (pos, dir), pre)))) = to_visit.pop() {
            let e = visited.entry(p).or_insert((
                usize::MAX,
                HashSet::<_, BuildHasherDefault<FxHasher>>::default(),
            ));
            match cost.cmp(&e.0) {
                Ordering::Less => {
                    e.0 = cost;
                    e.1.clear();
                    e.1.insert(pre);
                }
                Ordering::Equal => {
                    e.1.insert(pre);
                }
                Ordering::Greater => {
                    continue;
                }
            }
            if best < cost {
                continue;
            }
            if pos == self.goal {
                let root = DIRECTIONS
                    .iter()
                    .map(|d| (self.goal, *d))
                    .flat_map(|p| visited.get(&p))
                    .cloned()
                    .collect::<Vec<_>>();
                best = root[0].0;
                continue;
            }
            for d in DIRECTIONS.iter() {
                if let Some(q) = pos.add(d.as_vec2()).included((0, 0), self.size) {
                    if self.mapping[q] {
                        let c = cost + if dir == *d { 1 } else { 1001 };
                        to_visit.push(Reverse((c, ((*q, *d), p))));
                    }
                }
            }
        }
        count_points(&visited, self.goal)
    }
}
