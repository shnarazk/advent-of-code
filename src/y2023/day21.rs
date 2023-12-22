//! <https://adventofcode.com/2023/day/21>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::collections::HashSet;
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{neighbors, Dim2, GeometricMath},
        line_parser, progress, regex,
    },
    serde::Serialize,
    std::collections::HashMap,
};

const OBSERV: usize = 2;

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
    start: Dim2<usize>,
    history: HashMap<Dim2<usize>, Vec<usize>>,
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
    fn serialize(&self) {
        // add 1 for the firt element holding start time
        // sub 2 for the last element which is 2 blocks apart from the next base
        let estimated_time = 131 + 131 + 1 - 2;
        let v = (0..OBSERV)
            .map(|y| {
                (0..OBSERV)
                    .map(|x| {
                        let v = self.history.get(&(y, x)).map_or(Vec::new(), |r| r.clone());
                        if 262 < v.len() {
                            vec![v[..estimated_time].to_vec(), v[estimated_time..].to_vec()]
                        } else {
                            vec![v]
                        }
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        println!("{}", serde_json::to_string(&v).unwrap());
    }
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
        map.iter()
            .map(|l| l.iter().filter(|c| **c == steps).count())
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output1 {
        let limit = 26501365;
        let steps = 500;
        let height = self.line.len();
        let width = self.line[0].len();
        {
            // to upper right, the first quadrant
            let s = self.start;
            self.line[0..s.0].reverse();
            self.line[s.0..].reverse();
            self.line.reverse();
            for each in self.line.iter_mut() {
                each[0..s.1].reverse();
                each[s.1..].reverse();
                each.reverse();
            }
            self.start = (0, 0);
            assert!(self.line[0].iter().all(|n| !*n));
            assert!(self.line.iter().all(|v| !v[0]));
        }
        // dbg!(self.line.iter().map(|v| v.iter().filter(|p| !*p).count()).sum::<usize>());
        let mut to_visit: HashSet<Dim2<usize>> = HashSet::new();
        let mut next: HashSet<Dim2<usize>> = HashSet::new();
        to_visit.insert((self.start.0, self.start.1));
        self.history.insert((0, 0), vec![0, 1]);
        for n in 0..steps {
            progress!(n);
            let mut memo = [[0; 2 * OBSERV]; 2 * OBSERV];
            for p in to_visit.iter() {
                for q in p.neighbors4((0, 0), (limit, limit)).iter() {
                    if !self.line[q.0 % height][q.1 % width] && !next.contains(q) {
                        next.insert(*q);
                        let i = q.0 / height;
                        let j = q.1 / width;
                        if i < OBSERV && j < OBSERV {
                            memo[i][j] += 1;
                        }
                    }
                }
            }
            to_visit.clear();
            std::mem::swap(&mut to_visit, &mut next);
            for y in 0..OBSERV {
                for x in 0..OBSERV {
                    let reach = memo[y][x];
                    if 0 < reach {
                        self.history.entry((y, x)).or_insert(vec![n]).push(reach);
                    }
                }
            }
        }
        assert_eq!(
            to_visit.contains(&(0, 0)),
            to_visit.contains(&(131 + 1, 131 + 1))
        );
        self.serialize();
        let count = 0;
        count
    }
}
