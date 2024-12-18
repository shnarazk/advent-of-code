//! <https://adventofcode.com/2024/day/18>
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
    serde_json::to_value,
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap},
        hash::BuildHasherDefault,
    },
    winnow::{
        ascii::newline,
        combinator::{repeat, repeat_till, separated, seq, terminated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
    mapping: Rect<bool>,
    size: Vec2,
    bricks: usize,
}

fn parse_line(s: &mut &str) -> PResult<(usize, usize)> {
    seq!(parse_usize, _: ",", parse_usize).parse_next(s)
}
fn parse(s: &mut &str) -> PResult<Vec<(usize, usize)>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc(2024, 18)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        match &self.get_config().alt {
            Some(x) if *x == "0".to_string() => {
                self.size = (7, 7);
                self.bricks = 12;
            }
            _ => {
                self.size = (71, 71);
                self.bricks = 1024;
            }
        };
        self.mapping = Rect::new(self.size, true);
        for p in self.line.iter().take(self.bricks) {
            self.mapping[(p.1 as isize, p.0 as isize)] = false;
        }
        // println!("{}", &self.mapping.to_string());
    }
    fn part1(&mut self) -> Self::Output1 {
        // let mut ret: FxHashMap<usize, usize> = HashMap::<usize, usize, BuildHasherDefault<FxHasher>>::default();
        let start: Vec2 = (0, 0);
        let goal: Vec2 = self.size.sub(&(1, 1));
        let mut to_visit: BinaryHeap<Reverse<(usize, Vec2)>> = BinaryHeap::new();
        to_visit.push(Reverse((0, start)));
        let mut visited: Rect<bool> = self.mapping.map(|_| false);
        while let Some(Reverse((cost, p))) = to_visit.pop() {
            if p == goal {
                return cost;
            }
            if visited[p] {
                continue;
            }
            visited[p] = true;
            for q in p.neighbors4((0, 0), self.size).iter() {
                if self.mapping[q] {
                    to_visit.push(Reverse((cost + 1, *q)));
                }
            }
        }
        dbg!(goal);
        1
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
