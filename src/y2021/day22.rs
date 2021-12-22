//! <https://adventofcode.com/2021/day/22>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser,
    },
    lazy_static::lazy_static,
    regex::Regex,
    std::collections::HashMap,
};

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<(bool, isize, isize, isize, isize, isize, isize)>,
}

#[aoc(2021, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";

    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        lazy_static! {
            static ref PARSER: Regex = Regex::new(r"^(on|off) x=(-?[0-9]+)\.\.(-?[0-9]+),y=(-?[0-9]+)\.\.(-?[0-9]+),z=(-?[0-9]+)\.\.(-?[0-9]+)$").expect("wrong");
        }
        let segment = PARSER.captures(block).ok_or(ParseError)?;
        self.line.push((
            &segment[1] == "on",
            line_parser::to_isize(&segment[2])?,
            line_parser::to_isize(&segment[3])?,
            line_parser::to_isize(&segment[4])?,
            line_parser::to_isize(&segment[5])?,
            line_parser::to_isize(&segment[6])?,
            line_parser::to_isize(&segment[7])?,
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(self
            .line
            .iter()
            .map(|(_, x, _, y, _, z, _)| x.min(y).min(z))
            .min()
            .unwrap());
        dbg!(self
            .line
            .iter()
            .map(|(_, _, x, _, y, _, z)| x.max(y).max(z))
            .max()
            .unwrap());
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let offset = |p: isize| (p + 50isize) as usize;
        let mut grid: Vec<Vec<Vec<bool>>> = Vec::new();
        for k in 0..=101 {
            let mut v = Vec::new();
            for j in 0..=101 {
                let mut w = Vec::new();
                w.resize(101, false);
                v.push(w);
            }
            grid.push(v);
        }
        for (to, x1, x2, y1, y2, z1, z2) in self.line.iter() {
            print!("{}..{},{}..{},{}..{}", x1, x2, y1, y2, z1, z2);
            println!(
                " - {:?},{:?},{:?}",
                50 < *z1 || *z2 < -50,
                50 < *y1 || *y2 < -50,
                50 < *x1 || *x2 < -50,
            );
            assert!(x1 <= x2 && y1 <= y2 && z1 <= z2);
            if 50 < *z1 || *z2 < -50 {
                continue;
            }
            for z in (*z1).max(-50)..=(*z2).min(50) {
                if 50 < *y1 || *y2 < -50 {
                    continue;
                }
                for y in (*y1).max(-50)..=(*y2).min(50) {
                    if 50 < *x1 || *x2 < -50 {
                        continue;
                    }
                    for x in (*x1).max(-50)..=(*x2).min(50) {
                        grid[offset(z)][offset(y)][offset(x)] = *to;
                    }
                }
            }
        }
        grid.iter()
            .map(|v| {
                v.iter()
                    .map(|w| w.iter().filter(|b| **b).count())
                    .sum::<usize>()
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}


struct Voxel {
    ons: Vec<(usize, usize, usize, usize, usize, usize)>,
}

impl Voxel {
    
}
