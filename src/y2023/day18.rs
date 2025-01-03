//! <https://adventofcode.com/2023/day/18>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, GeometricMath},
    },
    itertools::Itertools,
    serde::Serialize,
    std::collections::{BinaryHeap, HashMap, HashSet},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
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
            for _ in 0..*dist {
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
        let revertyl: Vec<(isize, isize)> = dicy
            .iter()
            .sorted()
            .enumerate()
            .map(|(i, v)| (i as isize, *v))
            .collect::<Vec<(isize, isize)>>();
        let revertxl: Vec<(isize, isize)> = dicx
            .iter()
            .sorted()
            .enumerate()
            .map(|(i, v)| (i as isize, *v))
            .collect::<Vec<(isize, isize)>>();
        pos = (0, 0);
        pre = (
            2 * *converty.get(&0).unwrap(),
            2 * *convertx.get(&0).unwrap(),
        );
        for (dir, dist) in self.line2.iter() {
            pos.0 += dir.0 * (*dist as isize);
            pos.1 += dir.1 * (*dist as isize);
            let p = (
                2 * *converty.get(&pos.0).unwrap(),
                2 * *convertx.get(&pos.1).unwrap(),
            );
            match dir {
                (1, 0) => {
                    for y in pre.0..=p.0 {
                        map.insert((y, p.1), 1);
                    }
                }
                (-1, 0) => {
                    for y in p.0..=pre.0 {
                        map.insert((y, p.1), 1);
                    }
                }
                (0, 1) => {
                    for x in pre.1..=p.1 {
                        map.insert((p.0, x), 1);
                    }
                }
                (0, -1) => {
                    for x in p.1..=pre.1 {
                        map.insert((p.0, x), 1);
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
        for y in corner0.0..corner1.0 {
            for x in corner0.1..corner1.1 {
                map.entry((y, x)).or_insert(2);
            }
        }
        for patterny in revertyl.windows(2) {
            let [(y, ry0), (_, ry1)] = patterny else {
                panic!();
            };
            for patternx in revertxl.windows(2) {
                let [(x, rx0), (_, rx1)] = patternx else {
                    panic!();
                };
                if let Some(2) = map.get(&(2 * *y, 2 * *x)) {
                    amount += 1;
                }
                if let Some(2) = map.get(&(2 * *y + 1, 2 * *x)) {
                    amount += (ry1 - ry0 - 1) as usize;
                }
                if let Some(2) = map.get(&(2 * *y, 2 * *x + 1)) {
                    amount += (rx1 - rx0 - 1) as usize;
                }
                if let Some(2) = map.get(&(2 * *y + 1, 2 * *x + 1)) {
                    amount += ((ry1 - ry0 - 1) * (rx1 - rx0 - 1)) as usize;
                }
            }
        }
        amount
    }
    fn serialize(&self) -> Option<String> {
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
        pos = (0, 0);
        pre = (
            2 * *converty.get(&0).unwrap(),
            2 * *convertx.get(&0).unwrap(),
        );
        for (dir, dist) in self.line2.iter() {
            pos.0 += dir.0 * (*dist as isize);
            pos.1 += dir.1 * (*dist as isize);
            let p = (
                2 * *converty.get(&pos.0).unwrap(),
                2 * *convertx.get(&pos.1).unwrap(),
            );
            match dir {
                (1, 0) => {
                    for y in pre.0..=p.0 {
                        map.insert((y, p.1), 1);
                    }
                }
                (-1, 0) => {
                    for y in p.0..=pre.0 {
                        map.insert((y, p.1), 1);
                    }
                }
                (0, 1) => {
                    for x in pre.1..=p.1 {
                        map.insert((p.0, x), 1);
                    }
                }
                (0, -1) => {
                    for x in p.1..=pre.1 {
                        map.insert((p.0, x), 1);
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

        let a = (corner0.0..corner1.0)
            .map(|y| {
                (corner0.1..corner1.1)
                    .map(|x| *map.get(&(y, x)).unwrap_or(&0))
                    .collect::<Vec<usize>>()
            })
            .collect::<Vec<_>>();
        #[derive(Debug, Default, Eq, PartialEq, Serialize)]
        struct Dump {
            map: Vec<Vec<usize>>,
        }
        serde_json::to_string(&Dump { map: a }).ok()
    }
}
