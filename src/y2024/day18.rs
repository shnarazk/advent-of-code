//! <https://adventofcode.com/2024/day/18>
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::*,
        parser::parse_usize,
        rect::Rect,
    },
    serde::Serialize,
    std::{cmp::Reverse, collections::BinaryHeap},
    winnow::{
        ascii::newline,
        combinator::{separated, seq},
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

#[aoc_at(2024, 18)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        match &self.get_config().alt {
            Some(x) if x.as_str() == "0" => {
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
        // println!("{}", self.mapping);
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
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        // let mut index = dbg!(self.bricks);
        let mut range: (usize, usize) = (self.bricks, self.line.len());
        while range.0 + 1 != range.1 {
            let med = (range.0 + range.1) / 2;
            let mut you = self.clone();
            for p in you.line.iter().take(med) {
                you.mapping[(p.1 as isize, p.0 as isize)] = false;
            }
            // println!("{},{}", you.line[index - 1].0, you.line[index - 1].1);
            if you.part1() == 0 {
                range.1 = med;
            } else {
                range.0 = med;
            }
        }
        /* loop {
            index += 1;
            let mut you = self.clone();
            for p in you.line.iter().take(index) {
                you.mapping[(p.1 as isize, p.0 as isize)] = false;
            }
            // println!("{},{}", you.line[index - 1].0, you.line[index - 1].1);
            if you.part1() == 0 {
                break;
            }
        } */
        format!("{},{}", self.line[range.0].0, self.line[range.0].1)
    }
}
