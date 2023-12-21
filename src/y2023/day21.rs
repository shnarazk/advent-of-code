//! <https://adventofcode.com/2023/day/21>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{neighbors, Dim2, GeometricMath},
        line_parser, progress, regex,
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
    fn part2(&mut self) -> Self::Output1 {
        dbg!(self
            .line
            .iter()
            .map(|v| v.iter().filter(|p| !*p).count())
            .sum::<usize>());
        let height = self.line.len() as isize;
        let width = self.line[0].len() as isize;
        let steps = 500; // 2650u365;
        let mut to_visit: Vec<Dim2<isize>> = Vec::new();
        let mut next: Vec<Dim2<isize>> = Vec::new();
        let mut history: HashMap<Dim2<isize>, Vec<(usize, usize)>> = HashMap::new();
        to_visit.push((self.start.0 as isize, self.start.1 as isize));
        for n in 0..steps {
            progress!(n);
            let mut memo = [[0; 7]; 7];
            while let Some(p) = to_visit.pop() {
                for q in p
                    .neighbors4((isize::MIN, isize::MIN), (isize::MAX, isize::MAX))
                    .iter()
                {
                    let mod_y = abs_mod(q.0, height);
                    let mod_x = abs_mod(q.1, width);
                    if !self.line[mod_y][mod_x] && !next.contains(q) {
                        next.push(*q);
                        let i = if 0 <= q.0 {
                            q.0 / height
                        } else {
                            q.0 / height - 1
                        };
                        let j = if 0 <= q.1 {
                            q.1 / width
                        } else {
                            q.1 / width - 1
                        };
                        if -3 <= i && i < 4 && -3 <= j && j < 4 {
                            memo[(i + 3) as usize][(j + 3) as usize] += 1;
                        }
                    }
                }
            }
            std::mem::swap(&mut to_visit, &mut next);
            assert!(next.is_empty());
            for y in -3..=3 {
                for x in -3..=3 {
                    let reach = memo[(y + 3) as usize][(x + 3) as usize];
                    if 0 < reach {
                        let entry = history.entry((y, x)).or_default();
                        entry.push((n, reach));
                    }
                }
            }
        }
        for y in -3..=3 {
            for x in -3..=3 {
                let base = (y * height, x * width);
                let reach = to_visit
                    .iter()
                    .filter(|(yy, xx)| {
                        base.0 <= *yy
                            && *yy < base.0 + height
                            && base.1 <= *xx
                            && *xx < base.1 + width
                    })
                    .count();
                print!("{:10}", reach);
            }
            println!();
        }
        for y in -3..=3 {
            for x in -3..=3 {
                if let Some(v) = history.get(&(y, x)) {
                    let start = v[0].0;
                    let series = v.iter().map(|(t, n)| *n).collect::<Vec<_>>();
                    println!("({y},{x}) {start} | {:?}", series);
                } else {
                    println!("({y},{x}) -");
                }
            }
            println!();
        }

        let count = 0;
        count
    }
}

fn abs_mod(a: isize, b: isize) -> usize {
    let tmp = a % b;
    if 0 <= tmp {
        tmp as usize
    } else {
        (b + tmp) as usize
    }
}
