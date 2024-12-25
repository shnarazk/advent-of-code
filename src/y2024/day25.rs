//! <https://adventofcode.com/2024/day/25>
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        rect::Rect,
    },
    serde::Serialize,
    winnow::{
        ascii::newline,
        combinator::{repeat, separated},
        token::one_of,
        PResult, Parser,
    },
};

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    line: Vec<Rect<bool>>,
    locks: Vec<(usize, Vec<usize>)>,
    keys: Vec<(usize, Vec<usize>)>,
}

fn parse_line(s: &mut &str) -> PResult<Vec<bool>> {
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

fn parse_maze(s: &mut &str) -> PResult<Vec<Vec<bool>>> {
    separated(1.., parse_line, newline).parse_next(s)
}

fn parse(s: &mut &str) -> PResult<Vec<Vec<Vec<bool>>>> {
    separated(1.., parse_maze, (newline, newline)).parse_next(s)
}

#[aoc_at(2024, 25)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let line = parse(&mut input.as_str())?;
        self.line = line.into_iter().map(Rect::from_vec).collect::<Vec<_>>();
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for r in self.line.iter() {
            if r.iter().filter(|((i, _), _)| *i == 0).all(|(_, b)| *b) {
                let v = r.transpose().to_vec();
                let w = v
                    .iter()
                    .map(|l| l.iter().filter(|b| **b).count() - 1)
                    .collect::<Vec<_>>();
                println!("{w:?}");
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
                println!("{w:?}");
                self.keys.push((r.size.0 as usize, w));
            }
        }
        dbg!(&self.line.len());
        dbg!(&self.locks.len());
        dbg!(&self.keys.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut count = 0;
        for (h1, r) in self.locks.iter() {
            for (h2, k) in self.keys.iter() {
                assert_eq!(h1, h2);
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
        "Congraturations".to_string()
    }
}
