//! <https://adventofcode.com/2021/day/5>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, PartialEq)]
struct DataSegment {
    beg: (usize, usize),
    end: (usize, usize),
}

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<DataSegment>,
    max_x: usize,
    max_y: usize,
    count: Vec<Vec<usize>>,
}

mod parser {
    use {
        super::DataSegment,
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<DataSegment> {
        seq!(
            parse_usize, _: ",",parse_usize, _: " -> ",
            parse_usize, _: ",",parse_usize,
        )
        .map(|(a, b, c, d)| DataSegment {
            beg: (a, b),
            end: (c, d),
        })
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<DataSegment>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2021, 5)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        self.max_x = self
            .line
            .iter()
            .map(|ds| ds.beg.0.max(ds.end.0))
            .max()
            .unwrap_or(0);
        self.max_y = self
            .line
            .iter()
            .map(|ds| ds.beg.1.max(ds.end.1))
            .max()
            .unwrap_or(0);
        for _ in 0..=self.max_y {
            self.count.push(vec![0; self.max_x + 1]);
        }
        Ok(())
    }
    fn part1(&mut self) -> usize {
        for ds in self.line.iter() {
            if ds.beg.0 == ds.end.0 {
                let beg = ds.beg.1.min(ds.end.1);
                let end = ds.beg.1.max(ds.end.1);
                for i in beg..=end {
                    self.count[i][ds.beg.0] += 1;
                }
            } else if ds.beg.1 == ds.end.1 {
                let beg = ds.beg.0.min(ds.end.0);
                let end = ds.beg.0.max(ds.end.0);
                for i in beg..=end {
                    self.count[ds.beg.1][i] += 1;
                }
            } else {
                // dbg!(ds);
            }
        }
        // println!("{:?}", &self.count);
        self.count
            .iter()
            .map(|v| v.iter().filter(|x| 1 < **x).count())
            .sum()
    }
    fn part2(&mut self) -> usize {
        for ds in self.line.iter() {
            if ds.beg.0 == ds.end.0 {
                let beg = ds.beg.1.min(ds.end.1);
                let end = ds.beg.1.max(ds.end.1);
                for i in beg..=end {
                    self.count[i][ds.beg.0] += 1;
                }
            } else if ds.beg.1 == ds.end.1 {
                let beg = ds.beg.0.min(ds.end.0);
                let end = ds.beg.0.max(ds.end.0);
                for i in beg..=end {
                    self.count[ds.beg.1][i] += 1;
                }
            } else if (ds.beg.0 as isize - ds.end.0 as isize).abs()
                == (ds.beg.0 as isize - ds.end.0 as isize).abs()
            {
                let mut x: isize = ds.beg.0 as isize;
                let mut y: isize = ds.beg.1 as isize;
                let diff_x: isize = (ds.end.0 as isize - ds.beg.0 as isize).signum();
                let diff_y: isize = (ds.end.1 as isize - ds.beg.1 as isize).signum();
                for _ in 0..=(ds.end.0 as isize - ds.beg.0 as isize).abs() {
                    self.count[y as usize][x as usize] += 1;
                    x += diff_x;
                    y += diff_y;
                }
            }
        }
        // println!("{:?}", &self.count);
        self.count
            .iter()
            .map(|v| v.iter().filter(|x| 1 < **x).count())
            .sum()
    }
}
