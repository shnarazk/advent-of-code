//! <https://adventofcode.com/2023/day/14>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use itertools::assert_equal;
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
}

#[aoc(2023, 14)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(
            block
                .chars()
                .map(|c| match c {
                    'O' => 1,
                    '#' => 2,
                    _ => 0,
                })
                .collect::<Vec<_>>(),
        );
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        // dbg!(self.line.len(), self.line[0].len());
        count(&add_force(self.line.clone()))
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut map: HashMap<Vec<Vec<usize>>, usize> = HashMap::new();
        // dbg!(count(&add_force(self.line.clone())));
        let mut m = self.line.clone();
        map.insert(m.clone(), 0);
        // let mut val = 100000;
        // for _ in 0..50 {
        //     m = cycle(m);
        //     val = val.min(count(&m));
        //     // print(&m.clone());
        //     // print(&add_force(m.clone()));
        //     // println!();
        // }
        // dbg!(val);
        for i in 1.. {
            m = cycle(m);
            if let Some(j) = map.get(&m) {
                dbg!(i, j);
                let c = i - j;
                let remain1 = (1000000000 - i) - c * ((1000000000 - i) / c);
                let remain = (1000000000 - i) % c;
                assert_eq!(remain1, remain);
                dbg!(remain);
                for _ in 0..remain {
                    m = cycle(m);
                }
                return count(&m);
                // return i - j;
            }
            map.insert(m.clone(), i);
        }
        0
        // print(&cycle(cycle(cycle(self.line.clone()))));
        // 2
    }
}

fn transpose(v: &Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    let h = v.len();
    let w = v[0].len();
    (0..w)
        .map(|x| (0..h).map(|y| v[y][x]).collect::<Vec<_>>())
        .collect::<Vec<_>>()
}

fn add_force(mat: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    let m = transpose(&mat);
    let depth = m[0].len();
    let map = m
        .iter()
        .map(|line| {
            let mut res = Vec::new();
            let mut base = 0;
            for (i, k) in line.iter().enumerate() {
                match *k {
                    1 => {
                        res.push(base);
                        base += 1;
                    }
                    2 => base = i + 1,
                    _ => (),
                }
            }
            res
        })
        .collect::<Vec<_>>();
    let mut n = mat.clone();
    for l in n.iter_mut() {
        for p in l.iter_mut() {
            if *p == 1 {
                *p = 0;
            }
        }
    }
    for (x, l) in map.iter().enumerate() {
        for y in l.iter() {
            n[*y][x] = 1;
        }
    }
    n
}

fn rotate_clockwise(m: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    let h = m.len();
    let w = m[0].len();
    let mut n = m.clone();
    for (y, l) in n.iter_mut().enumerate() {
        for (x, p) in l.iter_mut().enumerate() {
            *p = m[h - x - 1][y];
        }
    }
    n
}

fn print(m: &Vec<Vec<usize>>) {
    for l in m.iter() {
        for p in l.iter() {
            print!(
                "{}",
                match p {
                    1 => 'O',
                    2 => '#',
                    _ => '.',
                }
            );
        }
        println!();
    }
}
fn cycle(m: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    rotate_clockwise(add_force(rotate_clockwise(add_force(rotate_clockwise(
        add_force(rotate_clockwise(add_force(m))),
    )))))
    // rotate_clockwise(rotate_clockwise(rotate_clockwise(rotate_clockwise(m))))
    // rotate_clockwise(rotate_clockwise(rotate_clockwise(rotate_clockwise(m))))
    // print(&m);
    // println!();
    // rotate_clockwise(m)
}

fn count(mat: &Vec<Vec<usize>>) -> usize {
    let depth = mat.len();
    let m = transpose(mat);
    m.iter()
        .map(|line| {
            let mut res = Vec::new();
            for (i, k) in line.iter().enumerate() {
                match *k {
                    1 => {
                        res.push(i);
                    }
                    _ => (),
                }
            }
            res.iter().map(|val| depth - val).sum::<usize>()
        })
        .sum::<usize>()
}
