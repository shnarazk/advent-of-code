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
        let mut at_least = 913;
        let set_x: HashSet<isize> = self
            .line
            .iter()
            .flat_map(|p| [p.0 .0 - p.1 as isize, p.0 .0, p.0 .0 + p.1 as isize])
            .collect::<HashSet<_>>();
        let cand_x = set_x
            .iter()
            .map(|x| {
                (
                    *x,
                    self.line
                        .iter()
                        .filter(|b| b.0 .0.abs_diff(*x) <= b.1)
                        .collect::<HashSet<_>>(),
                )
            })
            .filter(|(_, v)| at_least <= v.len())
            .collect::<HashMap<isize, HashSet<&Nanobot>>>();
        let set_y: HashSet<isize> = self
            .line
            .iter()
            .flat_map(|p| [p.0 .1 - p.1 as isize, p.0 .1, p.0 .1 + p.1 as isize])
            .collect::<HashSet<_>>();
        let cand_y = set_y
            .iter()
            .map(|y| {
                (
                    *y,
                    self.line
                        .iter()
                        .filter(|b| b.0 .1.abs_diff(*y) <= b.1)
                        .collect::<HashSet<_>>(),
                )
            })
            .filter(|(_, v)| at_least <= v.len())
            .collect::<HashMap<isize, HashSet<&Nanobot>>>();

        let set_z: HashSet<isize> = self
            .line
            .iter()
            .flat_map(|p| [p.0 .2 - p.1 as isize, p.0 .2, p.0 .2 + p.1 as isize])
            .collect::<HashSet<_>>();
        let cand_z = set_z
            .iter()
            .map(|z| {
                (
                    *z,
                    self.line
                        .iter()
                        .filter(|b| b.0 .2.abs_diff(*z) <= b.1)
                        .collect::<HashSet<_>>(),
                )
            })
            .filter(|(_, v)| at_least <= v.len())
            .collect::<HashMap<isize, HashSet<&Nanobot>>>();
        dbg!(cand_x.len(), cand_y.len(), cand_z.len());

        let mut best_p = (0, 0, 0);
        let mut most = 0;
        for (x, robots_x) in cand_x.iter() {
            if robots_x.len() < at_least {
                continue;
            }
            for (y, robots_y) in cand_y.iter() {
                if robots_y.len() < at_least {
                    continue;
                }
                let robots = robots_x
                    .iter()
                    .filter(|r| robots_y.contains(*r))
                    .copied()
                    .collect::<HashSet<_>>();
                if robots.len() < at_least {
                    continue;
                }
                for (z, robots_z) in cand_z.iter() {
                    if robots_z.len() < at_least {
                        continue;
                    }
                    let p = (*x, *y, *z);
                    let n = robots
                        .iter()
                        .filter(|r| robots_z.contains(*r))
                        .filter(|r| r.0.dist(&p) <= r.1)
                        .count();
                    match most.cmp(&n) {
                        std::cmp::Ordering::Less => {
                            most = n;
                            best_p = p;
                            if at_least < most {
                                at_least = most;
                            }
                            println!("{n:>4}/{at_least:>4}: {p:?}");
                        }
                        std::cmp::Ordering::Equal
                            if p.dist(&(0, 0, 0)) < best_p.dist(&(0, 0, 0)) =>
                        {
                            println!("         : {p:?}");
                            best_p = p;
                        }
                        _ => (),
                    }
                }
            }
        }
        best_p.dist(&(0, 0, 0))
    }
}
