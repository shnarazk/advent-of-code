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
    itertools::Itertools,
    std::collections::{BinaryHeap, HashMap, HashSet},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(Dim2<isize>, usize)>,
    line2: Vec<(Dim2<isize>, usize)>,
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
                2 => {
                    let str = b.trim().chars().collect::<Vec<char>>();
                    let dists = str.iter().skip(2).take(5).collect::<String>();
                    let dist = usize::from_str_radix(&dists, 16)?;
                    let dir = match str[7] {
                        '0' => (0, 1),
                        '1' => (1, 0),
                        '2' => (0, -1),
                        '3' => (-1, 0),
                        _ => unreachable!(),
                    };
                    self.line2.push((dir, dist));
                }
                _ => unreachable!(),
            }
        }
        self.line.push((dir, dist));
        Ok(())
    }
    // fn end_of_data(&mut self) {
    //     dbg!(&self.line.len());
    //     dbg!(&self.line2.len());
    // }
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
        ((corner1.0 - corner0.0) * (corner1.1 - corner0.1)) as usize
            - map.values().filter(|v| **v == 0).count()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut map: HashMap<Dim2<isize>, usize> = HashMap::new();
        let mut pos = (0, 0);
        let mut pre: Dim2<isize>;
        let mut corner0: Dim2<isize> = (0, 0);
        let mut corner1: Dim2<isize> = (0, 0);
        let mut dicy: HashSet<isize> = HashSet::new();
        let mut dicx: HashSet<isize> = HashSet::new();
        for (dir, dist) in self.line2.iter() {
            pos.0 += dir.0;
            pos.1 += dir.1;
            dicy.insert(pos.0);
            dicx.insert(pos.1);
            // corner0.0 = pos.0.min(corner0.0);
            // corner0.1 = pos.1.min(corner0.1);
            // corner1.0 = pos.0.max(corner1.0);
            // corner1.1 = pos.1.max(corner1.1);
        }
        let converty: HashMap<isize, isize> = dicy
            .iter()
            .sorted()
            .enumerate()
            .map(|(i, v)| (*v, i as isize))
            .collect::<HashMap<isize, isize>>();
        let convertx: HashMap<isize, isize> = dicx
            .iter()
            .sorted()
            .enumerate()
            .map(|(i, v)| (*v, i as isize))
            .collect::<HashMap<isize, isize>>();
        let reverty: HashMap<isize, isize> = dicy
            .iter()
            .sorted()
            .enumerate()
            .map(|(i, v)| (i as isize, *v))
            .collect::<HashMap<isize, isize>>();
        let revertx: HashMap<isize, isize> = dicx
            .iter()
            .sorted()
            .enumerate()
            .map(|(i, v)| (i as isize, *v))
            .collect::<HashMap<isize, isize>>();
        dbg!(converty.len());
        pos = (0, 0);
        pre = (0, 0);
        for (dir, dist) in self.line2.iter() {
            pos.0 += dir.0;
            pos.1 += dir.1;
            let p = (
                *converty.get(&pos.0).unwrap(),
                *convertx.get(&pos.1).unwrap(),
            );
            match (dir.0.signum(), dir.1.signum()) {
                (1, 0) => {
                    for y in pre.0..p.0 {
                        map.insert((y, p.1), 1);
                    }
                }
                (-1, 0) => {
                    for y in p.0..pre.0 {
                        map.insert((y, p.1), 1);
                    }
                }
                (0, 1) => {
                    for x in pre.0..p.0 {
                        map.insert((p.0, x), 1);
                    }
                }
                (0, -1) => {
                    for x in p.0..pre.0 {
                        map.insert((p.0, x), 1);
                    }
                }
                _ => unreachable!(),
            }

            map.insert(p, 1);
            corner0.0 = p.0.min(corner0.0);
            corner0.1 = p.1.min(corner0.1);
            corner1.0 = p.0.max(corner1.0);
            corner1.1 = p.1.max(corner1.1);
            pre = p;
        }
        corner0.0 -= 1;
        corner0.1 -= 1;
        corner1.0 += 2;
        corner1.1 += 2;
        dbg!(corner0, corner1);
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
        2
    }
}
