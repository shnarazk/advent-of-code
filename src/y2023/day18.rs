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
                    assert_eq!(str.len(), 9);
                    let dists = str.iter().skip(2).take(5).collect::<String>();
                    let dist = usize::from_str_radix(&dists, 16)?;
                    let dir = match str[7] {
                        '0' => (0, 1),
                        '1' => (1, 0),
                        '2' => (0, -1),
                        '3' => (-1, 0),
                        _ => unreachable!(),
                    };
                    // if self.line2.len() < 20 {
                    //     println!("{:?} {:?}", dir, dist);
                    // }
                    self.line2.push((dir, dist));
                }
                _ => unreachable!(),
            }
        }
        self.line.push((dir, dist));
        Ok(())
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
        let mut amount = 0;
        let mut map: HashMap<Dim2<isize>, usize> = HashMap::new();
        let mut pos = (0, 0);
        let mut pre: Dim2<isize>;
        let mut corner0: Dim2<isize> = pos;
        let mut corner1: Dim2<isize> = pos;
        let mut dicy: HashSet<isize> = HashSet::new();
        let mut dicx: HashSet<isize> = HashSet::new();
        dicy.insert(0);
        dicx.insert(0);
        dbg!(self.line2.len());
        for (dir, dist) in self.line2.iter() {
            pos.0 += dir.0 * (*dist as isize);
            pos.1 += dir.1 * (*dist as isize);
            dicy.insert(pos.0);
            dicx.insert(pos.1);
            amount += dist;
        }
        // println!("dicy: {:?}", dicy);
        let converty: HashMap<isize, isize> = dicy
            .iter()
            .sorted()
            .enumerate()
            .map(|(i, v)| (*v, i as isize))
            .collect::<HashMap<isize, isize>>();
        // println!("converty: {:?}", converty);
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
        let revertyl: Vec<(isize, isize)> = dicy
            .iter()
            .sorted()
            .enumerate()
            .map(|(i, v)| (i as isize, *v))
            .collect::<Vec<(isize, isize)>>();
        let revertx: HashMap<isize, isize> = dicx
            .iter()
            .sorted()
            .enumerate()
            .map(|(i, v)| (i as isize, *v))
            .collect::<HashMap<isize, isize>>();
        let revertxl: Vec<(isize, isize)> = dicx
            .iter()
            .sorted()
            .enumerate()
            .map(|(i, v)| (i as isize, *v))
            .collect::<Vec<(isize, isize)>>();
        pos = (0, 0);
        dbg!(converty.get(&0).unwrap(), convertx.get(&0).unwrap());
        pre = (
            2 * *converty.get(&0).unwrap(),
            2 * *convertx.get(&0).unwrap(),
        );
        // pre = (0, 0);
        for (dir, dist) in self.line2.iter() {
            pos.0 += dir.0 * (*dist as isize);
            pos.1 += dir.1 * (*dist as isize);
            let p = (
                2 * *converty.get(&pos.0).unwrap(),
                2 * *convertx.get(&pos.1).unwrap(),
            );
            assert!(0 <= p.0 && 0 <= p.1, "{:?}", p);
            match dir {
                (1, 0) => {
                    assert!(pre.0 <= p.0);
                    for y in pre.0..=p.0 {
                        map.insert((y, p.1), 1);
                        assert!(0 <= y, "{:?}", y);
                    }
                }
                (-1, 0) => {
                    assert!(p.0 <= pre.0);
                    for y in p.0..=pre.0 {
                        map.insert((y, p.1), 1);
                        assert!(0 <= y, "{:?}", y);
                    }
                }
                (0, 1) => {
                    assert!(pre.1 <= p.1);
                    for x in pre.1..=p.1 {
                        map.insert((p.0, x), 1);
                        assert!(0 <= x, "{:?}", x);
                    }
                }
                (0, -1) => {
                    assert!(p.1 <= pre.1);
                    for x in p.1..=pre.1 {
                        map.insert((p.0, x), 1);
                        assert!(0 <= x, "{:?}", x);
                    }
                }
                _ => unreachable!(),
            }

            corner0.0 = p.0.min(corner0.0);
            corner0.1 = p.1.min(corner0.1);
            corner1.0 = p.0.max(corner1.0);
            corner1.1 = p.1.max(corner1.1);
            pre = p;
        }
        corner0.0 -= 2;
        corner0.1 -= 2;
        corner1.0 += 2;
        corner1.1 += 2;
        for y in corner0.0..corner1.0 {
            for x in corner0.1..corner1.1 {
                print!(
                    "{}",
                    match map.get(&(y, x)) {
                        Some(1) => "#",
                        Some(0) => "x",
                        None => "_",
                        _ => "x",
                    }
                );
            }
            println!();
        }
        // println!("revertxl: {:?}", &revertxl);
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
        let mut fill = 0;
        for y in corner0.0..corner1.0 {
            for x in corner0.1..corner1.1 {
                if map.get(&(y, x)).is_none() {
                    map.insert((y, x), 2);
                    fill += 1;
                }
            }
            // println!();
        }
        dbg!(fill);
        dbg!(map.len());
        dbg!(map.values().filter(|v| **v == 0).count());
        dbg!(map.values().filter(|v| **v == 1).count());
        dbg!(map.values().filter(|v| **v == 2).count());
        // dbg!(map.keys().map(|c| c.0).min());
        // dbg!(map.keys().map(|c| c.1).min());
        // dbg!(&revertyl[0..3]);
        // for y in corner0.0..corner1.0 {
        //     for x in corner0.1..corner1.1 {
        //         print!(
        //             "{}",
        //             match map.get(&(y, x)) {
        //                 Some(1) => "#",
        //                 Some(0) => "_",
        //                 None => "?",
        //                 _ => "x",
        //             }
        //         );
        //     }
        //     println!();
        // }
        // for y in -1..revertyl.len() as isize * 2 {
        //     for x in -1..revertxl.len() as isize * 2 {
        //         print!(
        //             "{}",
        //             match map.get(&(y, x)) {
        //                 Some(1) => "#",
        //                 Some(0) => "_",
        //                 None => "?",
        //                 _ => "x",
        //             }
        //         );
        //     }
        //     println!();
        // }
        dbg!(amount);
        for patterny in revertyl.windows(2) {
            let [(y, ry0), (_, ry1)] = patterny else {
                panic!();
            };
            for patternx in revertxl.windows(2) {
                let [(x, rx0), (_, rx1)] = patternx else {
                    panic!();
                };
                // println!("{:?}", map.get(&(2 * *y, 2 * *x)));
                if let Some(2) = map.get(&(2 * *y, 2 * *x)) {
                    dbg!();
                    amount += 1;
                }
                if let Some(2) = map.get(&(2 * *y + 1, 2 * *x)) {
                    dbg!();
                    amount += (ry1 - ry0 - 1) as usize;
                }
                if let Some(2) = map.get(&(2 * *y, 2 * *x + 1)) {
                    dbg!();
                    amount += (rx1 - rx0 - 1) as usize;
                }
                if let Some(2) = map.get(&(2 * *y + 1, 2 * *x + 1)) {
                    println!(
                        " -> {}x{}={}",
                        ry1 - ry0 - 1,
                        rx1 - rx0 - 1,
                        (ry1 - ry0 - 1) * (rx1 - rx0 - 1)
                    );
                    amount += ((ry1 - ry0 - 1) * (rx1 - rx0 - 1)) as usize;
                }
            }
        }
        amount
    }
}
