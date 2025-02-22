//! <https://adventofcode.com/2024/day/25>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc_at},
        rect::Rect,
    },
    serde::Serialize,
    winnow::{
        ModalResult, Parser,
        ascii::newline,
        combinator::{repeat, separated},
        token::one_of,
    },
};

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    line: Vec<Rect<bool>>,
    locks: Vec<(usize, Vec<usize>)>,
    keys: Vec<(usize, Vec<usize>)>,
}

fn parse_line(s: &mut &str) -> ModalResult<Vec<bool>> {
    repeat(1.., one_of(&['#', '.']))
        .map(|v: String| {
            v.chars()
                .map(|c| match c {
                    '.' => false,
                    '#' => true,
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>()
        })
        .parse_next(s)
}

fn parse_maze(s: &mut &str) -> ModalResult<Vec<Vec<bool>>> {
    separated(1.., parse_line, newline).parse_next(s)
}

fn parse(s: &mut &str) -> ModalResult<Vec<Vec<Vec<bool>>>> {
    separated(1.., parse_maze, (newline, newline)).parse_next(s)
}

#[aoc_at(2024, 25)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        let line = parse(&mut input)?;
        self.line = line.into_iter().map(Rect::from_vec).collect::<Vec<_>>();
        for r in self.line.iter() {
            if r.iter().filter(|((i, _), _)| *i == 0).all(|(_, b)| *b) {
                let v = r.transpose().to_vec();
                let w = v
                    .iter()
                    .map(|l| l.iter().filter(|b| **b).count() - 1)
                    .collect::<Vec<_>>();
                self.locks.push((r.size.0 as usize, w));
            } else if r
                .iter()
                .filter(|((i, _), _)| *i + 1 == r.size.0)
                .all(|(_, b)| *b)
            {
                let v = r.transpose().to_vec();
                let w = v
                    .iter()
                    .map(|l| l.iter().filter(|b| **b).count() - 1)
                    .collect::<Vec<_>>();
                self.keys.push((r.size.0 as usize, w));
            }
        }
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut count = 0;
        for (h1, r) in self.locks.iter() {
            for (h2, k) in self.keys.iter() {
                debug_assert_eq!(h1, h2);
                let h = h1 - 2;
                if r.iter().enumerate().all(|(i, a)| *a + k[i] <= h) {
                    // println!("o h{h} {:?} - {:?}", r, k);
                    count += 1;
                } else {
                    // println!("x h{h} {:?} - {:?}", r, k);
                }
            }
        }
        count
    }
    fn part2(&mut self) -> Self::Output2 {
        "Congraturations!!".to_string()
    }
}
