//! <https://adventofcode.com/2022/day/23>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, GeometricMath},
    },
    std::collections::{HashMap, HashSet},
};

type Dim = Dim2<isize>;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
    map: HashSet<Dim>,
}

#[aoc(2022, 23)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn parse_block(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c == '#').collect::<Vec<_>>());
        Ok(())
    }
    fn end_of_data(&mut self) {
        for (j, l) in self.line.iter().rev().enumerate() {
            for (i, c) in l.iter().enumerate() {
                if *c {
                    self.map.insert((j as isize, i as isize));
                }
            }
        }
    }
    #[allow(dead_code)]
    fn dump(&self) {
        println!("[");
        let end = self.map.len();
        for (i, pos) in self.map.iter().enumerate() {
            print!("{{ \"y\": {}, \"x\": {}}}", pos.0, pos.1);
            if i + 2 <= end {
                print!(", ");
            }
            println!();
        }
        println!("]");
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
        // self.print();
        for _ in 0..10 {
            let mut targets: HashMap<Dim, Dim> = HashMap::new();
            'next_elf: for pos in self.map.iter() {
                if check_all.iter().any(|d| self.map.contains(&pos.add(d))) {
                    for d in 0..4 {
                        let dir = (target_base + d) % 4;
                        if check_list[dir]
                            .iter()
                            .map(|d| pos.add(d))
                            .all(|p| !self.map.contains(&p))
                        {
                            targets.insert(*pos, pos.add(target[dir]));
                            continue 'next_elf;
                        }
                    }
                }
                targets.insert(*pos, *pos);
            }
            let mut counts: HashMap<Dim, usize> = HashMap::new();
            for target in targets.values() {
                *counts.entry(*target).or_insert(0) += 1;
            }
            let mut next: HashSet<Dim> = HashSet::new();
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
            // if round < 5 {
            //     self.print();
            // }
        }
        // self.print();
        self.empties()
    }
    fn part2(&mut self) -> Self::Output2 {
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
        for round in 1.. {
            let mut targets: HashMap<Dim, Dim> = HashMap::new();
            'next_elf: for pos in self.map.iter() {
                if check_all.iter().any(|d| self.map.contains(&pos.add(d))) {
                    for d in 0..4 {
                        let dir = (target_base + d) % 4;
                        if check_list[dir]
                            .iter()
                            .map(|d| pos.add(d))
                            .all(|p| !self.map.contains(&p))
                        {
                            targets.insert(*pos, pos.add(target[dir]));
                            continue 'next_elf;
                        }
                    }
                }
                targets.insert(*pos, *pos);
            }
            let mut counts: HashMap<Dim, usize> = HashMap::new();
            for target in targets.values() {
                *counts.entry(*target).or_insert(0) += 1;
            }
            let mut next: HashSet<Dim> = HashSet::new();
            let mut moved = false;
            for from in self.map.iter() {
                if let Some(to) = targets.get(from) {
                    if *counts.get(to).unwrap() == 1 {
                        moved |= from != to;
                        next.insert(*to);
                        continue;
                    }
                }
                next.insert(*from);
            }
            if !moved {
                return round;
            }
            std::mem::swap(&mut self.map, &mut next);
            target_base = (target_base + 1) % 4;
        }
        unreachable!()
    }
}

impl Puzzle {
    #[allow(dead_code)]
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
