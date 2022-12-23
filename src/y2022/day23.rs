//! <https://adventofcode.com/2022/day/23>
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

type Dim2 = (isize, isize);

trait GeometricMove {
    fn add(&self, other: &Self) -> Self;
}

impl GeometricMove for Dim2 {
    fn add(&self, other: &Self) -> Self {
        (self.0 + other.0, self.1 + other.1)
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
    map: HashSet<Dim2>,
}

#[aoc(2022, 23)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c == '#').collect::<Vec<_>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        for (j, l) in self.line.iter().rev().enumerate() {
            for (i, c) in l.iter().enumerate() {
                if *c {
                    self.map.insert((j as isize, i as isize));
                }
            }
        }
        dbg!(&self.map.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let check_all = [
            (1, -1),
            (1, 0),
            (1, 1),
            (0, -1),
            (0, 1),
            (-1, -1),
            (-1, 0),
            (-1, 1),
        ];
        let target = [(1, 0), (-1, 0), (0, -1), (0, 1)];
        let check_list = [
            [(1, -1), (1, 0), (1, 1)],
            [(-1, -1), (-1, 0), (-1, 1)],
            [(1, -1), (0, -1), (-1, -1)],
            [(1, 1), (0, 1), (-1, 1)],
        ];
        let mut target_base = 0;
        self.print();
        for round in 0..10 {
            let mut targets: HashMap<Dim2, Dim2> = HashMap::new();
            'next_elf: for pos in self.map.iter() {
                if check_all.iter().any(|d| self.map.contains(&pos.add(d))) {
                    for d in 0..4 {
                        let dir = (target_base + d) % 4;
                        if check_list[dir]
                            .iter()
                            .map(|d| pos.add(d))
                            .all(|p| !self.map.contains(&p))
                        {
                            targets.insert(*pos, pos.add(&target[dir]));
                            continue 'next_elf;
                        }
                    }
                }
                targets.insert(*pos, *pos);
            }
            let mut counts: HashMap<Dim2, usize> = HashMap::new();
            for target in targets.values() {
                *counts.entry(*target).or_insert(0) += 1;
            }
            let mut next: HashSet<Dim2> = HashSet::new();
            for from in self.map.iter() {
                if let Some(to) = targets.get(from) {
                    if *counts.get(to).unwrap() == 1 {
                        next.insert(*to);
                        continue;
                    }
                }
                next.insert(*from);
            }
            std::mem::swap(&mut self.map, &mut next);
            target_base = (target_base + 1) % 4;
            if round < 5 {
                self.print();
            }
        }
        self.print();
        self.empties()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}

impl Puzzle {
    fn print(&self) {
        let min_y = self.map.iter().map(|(y, _)| *y).min().unwrap();
        let max_y = self.map.iter().map(|(y, _)| *y).max().unwrap();
        let min_x = self.map.iter().map(|(_, x)| *x).min().unwrap();
        let max_x = self.map.iter().map(|(_, x)| *x).max().unwrap();
        for j in (min_y..=max_y).rev() {
            for i in min_x..=max_x {
                print!("{}", if self.map.contains(&(j, i)) { '#' } else { '.' });
            }
            println!();
        }
        println!();
    }
    fn empties(&self) -> usize {
        let min_y = self.map.iter().map(|(y, _)| *y).min().unwrap();
        let max_y = self.map.iter().map(|(y, _)| *y).max().unwrap();
        let min_x = self.map.iter().map(|(_, x)| *x).min().unwrap();
        let max_x = self.map.iter().map(|(_, x)| *x).max().unwrap();
        (min_y..=max_y)
            .map(|j| {
                (min_x..=max_x)
                    .filter(|i| !self.map.contains(&(j, *i)))
                    .count()
            })
            .sum()
    }
}
