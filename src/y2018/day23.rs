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
                    (*pos, 0),
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
        let mut dist = max_position.dist(&(0, 0, 0));
        dbg!(dist);

        let range_x0 = self
            .line
            .iter()
            .filter(|r| r.0.dist(&max_position) <= r.1)
            .filter(|r| r.0 .0 < max_position.0)
            .map(|r| r.1 - r.0.dist(&max_position))
            .min()
            .unwrap();
        let range = 400;
        dbg!(range);
        for x in -(range as isize)..(range as isize) {
            for y in -(range as isize)..(range as isize) {
                for z in -(range as isize)..(range as isize) {
                    let p = (max_position.0 + x, max_position.1 + y, max_position.2 + z);
                    let offset = (x, y, z);
                    let c = self.line.iter().filter(|r| r.0.dist(&p) <= r.1).count();
                    let d0 = p.dist(&(0, 0, 0));
                    if max_count < c {
                        println!("not most {} => {} {:?}", c, d0, offset);
                        max_count = c;
                    } else if c == max_count && d0 < dist {
                        println!("not shortest => {}: {:?}", d0, offset);
                        dist = d0;
                    }
                    // assert!(max_count < c || dist < p.dist(&(0, 0, 0)));
                }
            }
        }
        dist
    }
}
