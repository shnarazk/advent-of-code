//! <https://adventofcode.com/2023/day/21>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{neighbors, Dim2, GeometricMath},
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
    start: Dim2<usize>,
}

#[aoc(2023, 21)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        if let Some(i) = block.chars().enumerate().find(|(i, c)| *c == 'S') {
            self.start = (self.line.len(), i.0);
        }
        self.line
            .push(block.chars().map(|c| c == '#').collect::<Vec<_>>());
        Ok(())
    }
    fn end_of_data(&mut self) {}
    fn part1(&mut self) -> Self::Output1 {
        let steps = 64;
        let height = self.line.len();
        let width = self.line[0].len();
        let mut to_visit: Vec<Dim2<usize>> = Vec::new();
        let mut next: Vec<Dim2<usize>> = Vec::new();
        to_visit.push(self.start);
        let mut map = self
            .line
            .iter()
            .map(|l| l.iter().map(|_| usize::MAX).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        for n in 0..=steps {
            while let Some(p) = to_visit.pop() {
                if self.line[p.0][p.1] {
                    continue;
                }
                map[p.0][p.1] = n;
                for q in p.neighbors4((0, 0), (height, width)).iter() {
                    if !next.contains(q) {
                        next.push(*q);
                    }
                }
            }
            std::mem::swap(&mut to_visit, &mut next);
        }
        // println!("{:?}", map);
        // for (y, l) in map.iter().enumerate() {
        //     for (x, c) in l.iter().enumerate() {
        //         print!(
        //             "{}",
        //             if self.line[y][x] {
        //                 '#'
        //             } else if *c == usize::MAX {
        //                 ' '
        //             } else {
        //                 (b'0' + *c as u8) as char
        //             }
        //         );
        //     }
        //     println!();
        // }
        map.iter()
            .map(|l| l.iter().filter(|c| **c == steps).count())
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
