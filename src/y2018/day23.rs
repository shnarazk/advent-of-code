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

trait InArea {
    fn in_range(&self, target: &Dim3) -> bool;
}

impl InArea for Nanobot {
    fn in_range(&self, target: &Dim3) -> bool {
        self.0.dist(target) <= self.1
    }
}

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
                ]
            })
            .collect::<HashMap<Dim3, usize>>();
        let mut max_count = 0;
        let mut max_positions = Vec::new();
        for robot in self.line.iter() {
            for (pos, count) in positions.iter_mut() {
                if robot.0.dist(pos) <= robot.1 {
                    *count += 1;
                    match max_count.cmp(count) {
                        std::cmp::Ordering::Less => {
                            max_count = *count;
                            max_positions.clear();
                            max_positions.push(*pos);
                        }
                        std::cmp::Ordering::Equal => {
                            max_positions.push(*pos);
                        }
                        _ => (),
                    }
                }
            }
        }
        dbg!(&max_positions, max_count);
        let base = max_positions[0];
        let mut range_min = usize::MAX;
        for robot in self.line.iter() {
            if robot.in_range(&base) {
                range_min = range_min.min(robot.1);
            }
        }
        dbg!(range_min);
        for x in 0..200 {
            for y in 0..200 {
                for z in 0..200 {
                    let p = (
                        base.0 - x as isize,
                        base.1 - y as isize,
                        base.2 - z as isize,
                    );
                    let count = self
                        .line
                        .iter()
                        .filter(|robot| robot.0.dist(&p) <= robot.1)
                        .count();
                    if max_count < count {
                        panic!();
                    }
                }
            }
        }
        // let dist = max_position.dist(&(0, 0, 0));
        // dist
        0
    }
}

const DIRS: [Dim3; 6] = [
    (-1, 0, 0),
    (1, 0, 0),
    (0, -1, 0),
    (0, 1, 0),
    (0, 0, -1),
    (0, 0, 1),
];

const NUM_ROBOTS: usize = 1000;

#[derive(Debug)]
struct Partition {
    center: Dim3,
    radius: usize,
    includes: usize,
    membership: [[bool; NUM_ROBOTS]; 6],
}

impl Partition {
    fn build_membership(&mut self, world: &Puzzle) {
        todo!()
    }
    fn isolated(&self) -> Option<usize> {
        (self.includes == 0
            && self.membership[1..]
                .iter()
                .all(|m| *m == self.membership[0]))
        .then(|| self.membership[0].iter().filter(|b| **b).count())
    }
    fn divide(&self) -> [Partition; 6] {
        let c = self.center;
        let radius = self.radius / 2;
        [
            Partition {
                center: (c.0 - radius as isize, c.1, c.2),
                radius,
                includes: 0,
                membership: [[false; NUM_ROBOTS]; 6],
            },
            Partition {
                center: (c.0 + radius as isize, c.1, c.2),
                radius,
                includes: 0,
                membership: [[false; NUM_ROBOTS]; 6],
            },
            Partition {
                center: (c.0, c.1 - radius as isize, c.2),
                radius,
                includes: 0,
                membership: [[false; NUM_ROBOTS]; 6],
            },
            Partition {
                center: (c.0, c.1 + radius as isize, c.2),
                radius,
                includes: 0,
                membership: [[false; NUM_ROBOTS]; 6],
            },
            Partition {
                center: (c.0, c.1, c.2 - radius as isize),
                radius,
                includes: 0,
                membership: [[false; NUM_ROBOTS]; 6],
            },
            Partition {
                center: (c.0, c.1, c.2 + radius as isize),
                radius,
                includes: 0,
                membership: [[false; NUM_ROBOTS]; 6],
            },
        ]
    }
}
