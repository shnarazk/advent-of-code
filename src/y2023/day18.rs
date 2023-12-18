//! <https://adventofcode.com/2023/day/18>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::geometric::neighbors8;
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{neighbors, Dim2, Direction, GeometricMath},
    },
    std::collections::{BinaryHeap, HashMap},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(Dim2<isize>, usize)>,
}

#[aoc(2023, 18)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let mut dir: Dim2<isize> = (0, 0);
        let mut dist = 0;
        for (i, b) in block.split(' ').enumerate() {
            match i {
                0 => {
                    dir = match b {
                        "U" => (-1, 0),
                        "L" => (0, -1),
                        "R" => (0, 1),
                        "D" => (1, 0),
                        _ => unreachable!(),
                    }
                }
                1 => dist = b.parse::<usize>().unwrap(),
                _ => (),
            }
        }
        self.line.push((dir, dist));
        Ok(())
    }
    fn end_of_data(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut map: HashMap<Dim2<isize>, usize> = HashMap::new();
        let mut pos = (1, 1);
        let mut corner0: Dim2<isize> = (0, 0);
        let mut corner1: Dim2<isize> = (0, 0);
        for (dir, dist) in self.line.iter() {
            for n in 0..*dist {
                pos.0 += dir.0;
                pos.1 += dir.1;
                map.insert(pos, 1);
                corner0.0 = pos.0.min(corner0.0);
                corner0.1 = pos.1.min(corner0.1);
                corner1.0 = pos.0.max(corner1.0);
                corner1.1 = pos.1.max(corner1.1);
            }
        }
        corner0.0 -= 1;
        corner0.1 -= 1;
        corner1.0 += 2;
        corner1.1 += 2;
        dbg!(corner0, corner1);
        let mut to_visit: BinaryHeap<Dim2<isize>> = BinaryHeap::new();
        to_visit.push(corner0);
        while let Some(p) = to_visit.pop() {
            if map.contains_key(&p) {
                continue;
            }
            map.insert(p, 0);
            for q in p.neighbors8(corner0, corner1).iter() {
                to_visit.push(*q);
            }
        }
        /*
        for y in corner0.0..corner1.0 {
            for x in corner0.1..corner1.1 {
                print!(
                    "{}",
                    match map.get(&(y, x)) {
                        Some(1) => "#",
                        Some(0) => "_",
                        None => "?",
                        _ => "x",
                    }
                );
            }
            println!();
        }
        */
        // 8 * 11
        dbg!(((corner1.0 - corner0.0) * (corner1.1 - corner0.1)) as usize)
            - map.values().filter(|v| **v == 0).count()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
