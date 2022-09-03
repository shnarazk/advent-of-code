//! <https://adventofcode.com/2018/day/23>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{HashMap, HashSet},
};

trait Geometry {
    fn x(&self) -> isize;
    fn y(&self) -> isize;
    fn z(&self) -> isize;
    fn dist(&self, other: &Self) -> usize;
    fn dist_1d(&self, other: &Self) -> usize;
    fn lift(&self) -> Dim3;
    fn unlift(&self) -> Dim3;
}

type Dim3 = (isize, isize, isize);

impl Geometry for Dim3 {
    fn x(&self) -> isize {
        self.0
    }
    fn y(&self) -> isize {
        self.1
    }
    fn z(&self) -> isize {
        self.2
    }
    fn dist(&self, other: &Dim3) -> usize {
        (self.0 - other.0).unsigned_abs()
            + (self.1 - other.1).unsigned_abs()
            + (self.2 - other.2).unsigned_abs()
    }
    fn dist_1d(&self, other: &Dim3) -> usize {
        (self.0 - other.0)
            .unsigned_abs()
            .min((self.1 - other.1).unsigned_abs())
            .min((self.2 - other.2).unsigned_abs())
    }
    fn lift(&self) -> Dim3 {
        (
            self.0 + self.1 + 2 * self.2, // a
            2 * (self.1 - self.0),        // y
            2 * self.2 - self.0 - self.1, // z
        )
    }
    fn unlift(&self) -> Dim3 {
        (
            (self.0 - self.1 - self.2) / 4,
            (self.1 + self.2 - self.0) / 4,
            (self.2 + self.0 - self.1) / 4,
        )
    }
}

type Nanobot = ((isize, isize, isize), usize);

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Nanobot>,
}

#[aoc(2018, 23)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^pos=<(-?\d+),(-?\d+),(-?\d+)>, r=(-?\d+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            (
                segment[1].parse::<isize>()?,
                segment[2].parse::<isize>()?,
                segment[3].parse::<isize>()?,
            ),
            segment[4].parse::<usize>()?,
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(self.line.len());
        // let m = (
        //     self.line.iter().map(|p| p.0 .0).max().unwrap(),
        //     self.line.iter().map(|p| p.0 .1).max().unwrap(),
        //     self.line.iter().map(|p| p.0 .2).max().unwrap(),
        //     self.line.iter().map(|p| p.1).max().unwrap(),
        //     self.line.iter().map(|p| p.1).min().unwrap(),
        // );
        // dbg!(m);
    }
    fn part1(&mut self) -> Self::Output1 {
        let strongest: (&usize, &Dim3) = self.line.iter().map(|(p, r)| (r, p)).max().unwrap();
        self.line
            .iter()
            .filter(|(p, r)| strongest.1.dist(p) <= *strongest.0)
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        println!("X-axis");
        for i in 0..5_isize {
            println!(
                "{:?} => {:?} => {:?}",
                (i, i, i),
                (i, i, i).lift(),
                (i, i, i).lift().unlift()
            );
        }
        println!("Y-axis");
        for i in 0..5_isize {
            println!(
                "{:?} => {:?} => {:?}",
                (-i, i, 0),
                (-i, i, 0).lift(),
                (-i, i, 0).lift().unlift()
            );
        }
        println!("Z-axis");
        for i in 0..5_isize {
            println!(
                "{:?} => {:?} => {:?}",
                (-i, -i, i),
                (-i, -i, i).lift(),
                (-i, -i, i).lift().unlift()
            );
        }
        println!();
        for y in (0..5).rev() {
            print!("{y}: ");
            for x in 0..5 {
                print!("{:?} ", (x, y, 0).lift());
            }
            println!();
        }
        for y in (0..5).rev() {
            print!("{y}: ");
            for x in 0..5 {
                print!("{:?} ", (x, y, 0).lift().unlift());
            }
            println!();
        }
        let mut positions: HashMap<Dim3, usize> = self
            .line
            .iter()
            .flat_map(|(pos, r)| {
                [
                    ((pos.0 - *r as isize, pos.1, pos.2), 0),
                    ((pos.0 + *r as isize, pos.1, pos.2), 0),
                    ((pos.0, pos.1 - *r as isize, pos.2), 0),
                    ((pos.0, pos.1 + *r as isize, pos.2), 0),
                    ((pos.0, pos.1, pos.2 - *r as isize), 0),
                    ((pos.0, pos.1, pos.2 + *r as isize), 0),
                ]
            })
            .collect::<HashMap<Dim3, usize>>();
        let mut max_count = 0;
        let mut max_position = (0, 0, 0);
        for robot in self.line.iter() {
            for (pos, count) in positions.iter_mut() {
                if robot.0.dist(pos) <= robot.1 {
                    *count += 1;
                    if max_count < *count {
                        max_count = *count;
                        max_position = *pos;
                    } else if max_count == *count
                        && pos.dist(&(0, 0, 0)) < max_position.dist(&(0, 0, 0))
                    {
                        max_position = *pos;
                    }
                }
            }
        }
        dbg!(max_position, max_count);
        let dist = max_position.dist(&(0, 0, 0));
        dbg!(dist)
    }
}
