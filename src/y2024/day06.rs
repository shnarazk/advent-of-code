//! <https://adventofcode.com/2024/day/6>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::*,
        rect::Rect,
    },
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashMap, FxHashSet, FxHasher},
    serde::Serialize,
    std::{collections::HashSet, hash::BuildHasherDefault},
    winnow::{
        ModalResult, Parser,
        ascii::newline,
        combinator::{repeat, separated},
        token::one_of,
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

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    mapping: Vec<Vec<char>>,
    plane: Rect<bool>,
    guard: (Vec2, Direction),
    size: Vec2,
    trail: FxHashMap<Vec2, Option<(Vec2, Direction)>>,
}

impl Puzzle {
    fn next_pos(&mut self) -> Option<Vec2> {
        let p = self.guard.0.add(self.guard.1.as_vec2());
        ((0..self.size.0).contains(&p.0) && (0..self.size.1).contains(&p.1)).then_some(p)
    }
    fn turn(&mut self) {
        self.guard.1 = self.guard.1.turn_right();
    }
    fn is_loop(&mut self, pos: Vec2, pre: (Vec2, Direction)) -> bool {
        self.plane[&pos] = true;
        let mut trail: FxHashSet<(Vec2, Direction)> =
            HashSet::<(Vec2, Direction), BuildHasherDefault<FxHasher>>::default();
        self.guard = pre;
        let mut pos = Some(self.guard.0);
        while let Some(p) = pos {
            self.guard.0 = p;
            if trail.contains(&self.guard) {
                return true;
            }
            trail.insert(self.guard);
            pos = self.next_pos();
            if let Some(p) = pos {
                if self.plane[&p] {
                    self.turn();
                    pos = self.next_pos();
                    if let Some(p) = pos {
                        if self.plane[&p] {
                            self.turn();
                            pos = self.next_pos();
                        }
                    }
                    // There is no possibility of U-shaped obstructions!
                }
            }
        }
        false
    }
}

fn parse_line(input: &mut &str) -> ModalResult<Vec<char>> {
    repeat(1.., one_of(['.', '#', '<', '^', '>', 'v'])).parse_next(input)
}

fn parse(input: &mut &str) -> ModalResult<Vec<Vec<char>>> {
    separated(1.., parse_line, newline).parse_next(input)
}

#[aoc(2024, 6)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.mapping = parse(&mut input)?;
        self.size.0 = self.mapping.len() as isize;
        self.size.1 = self.mapping[0].len() as isize;
        self.plane = Rect::new(self.size, false);
        for (i, l) in self.mapping.iter().enumerate() {
            for (j, c) in l.iter().enumerate() {
                let pos = (i as isize, j as isize);
                match kind_from(c) {
                    Kind::Guard(d) => {
                        self.guard = (pos, d);
                    }
                    Kind::Obst => {
                        self.plane[&pos] = true;
                    }
                    _ => (),
                }
            }
        }
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut pos = Some(self.guard.0);
        self.trail.insert(self.guard.0, None);
        while let Some(p) = pos {
            if let std::collections::hash_map::Entry::Vacant(e) = self.trail.entry(p) {
                e.insert(Some(self.guard));
            }
            self.guard.0 = p;
            pos = self.next_pos();
            if let Some(p) = pos {
                if self.plane[&p] {
                    self.turn();
                    pos = self.next_pos();
                    // there's no chains of obstructions.
                    // if let Some(p) = pos {
                    //     if self.hash.contains(&p) {
                    //         self.turn();
                    //         pos = self.next_pos();
                    //     }
                    // }
                }
            }
        }
        self.trail.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut me = self.clone();
        me.part1();
        me.trail
            .par_iter()
            .filter(|(p, pre)| pre.is_some_and(|pre| self.clone().is_loop(**p, pre)))
            .count()
    }
}
