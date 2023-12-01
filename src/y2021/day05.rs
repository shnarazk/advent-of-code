//! <https://adventofcode.com/2021/day/5>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

#[derive(Debug, PartialEq)]
struct DataSegment {
    beg: (usize, usize),
    end: (usize, usize),
}

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<DataSegment>,
    max_x: usize,
    max_y: usize,
    count: Vec<Vec<usize>>,
}

#[aoc(2021, 5)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let mut i = DataSegment {
            beg: (0, 0),
            end: (0, 0),
        };
        let parser = regex!(r"^([0-9]+),([0-9]+) -> ([0-9]+),([0-9]+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        i.beg.0 = segment[1].parse::<usize>()?;
        i.beg.1 = segment[2].parse::<usize>()?;
        i.end.0 = segment[3].parse::<usize>()?;
        i.end.1 = segment[4].parse::<usize>()?;
        self.line.push(i);
        Ok(())
    }
    fn end_of_data(&mut self) {
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
            let mut v = Vec::new();
            v.resize(self.max_x + 1, 0);
            self.count.push(v);
        }
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
