//! <https://adventofcode.com/2017/day/21>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

type Rule = HashMap<Vec<bool>, Vec<bool>>;

enum Divided {
    By2(Vec<Plane2>),
    By3(Vec<Plane3>),
    None,
}
#[derive(Clone, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Plane {
    size: usize,
    plane: Vec<bool>,
}

impl std::fmt::Debug for Plane {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, b) in self.plane.iter().enumerate() {
            let _ = write!(f, "{}", if *b { '#' } else { '.' });
            if (i + 1) % self.size == 0 {
                let _ = writeln!(f);
            }
        }
        Ok(())
    }
}
impl Plane {
    fn divide(&self, rule: &Rule) -> Divided {
        if self.size % 2 == 0 {
            let mut result = Vec::new();
            for index in 0..(self.size / 2).pow(2) {
                let j_start = 2 * (index % (self.size / 2));
                let i_start = 2 * (index / (self.size / 2));
                let mut pack: Vec<bool> = vec![];
                for j in 0..2 {
                    for i in 0..2 {
                        pack.push(self.plane[j_start + j * self.size + i_start + i]);
                    }
                }
                result.push(Plane2(vec![pack[0], pack[1], pack[2], pack[3]]));
            }
            return Divided::By2(result);
        } else if self.size % 3 == 0 {
            let mut result = Vec::new();
            for index in 0..(self.size / 3).pow(2) {
                let j_start = (self.size * 3) * (index / (self.size / 3));
                let i_start = 3 * (index % (self.size / 3));
                let mut pack: Vec<bool> = vec![];
                for j in 0..3 {
                    for i in 0..3 {
                        pack.push(self.plane[j_start + j * self.size + i_start + i]);
                    }
                }
                result.push(Plane3(vec![
                    pack[0], pack[1], pack[2], pack[3], pack[4], pack[5], pack[6], pack[7], pack[8],
                ]));
            }
            return Divided::By3(result);
        }
        Divided::None
    }
    fn extend(&self, rule: &Rule) -> Option<Plane> {
        match self.divide(rule) {
            Divided::By2(tiles) => {
                let mut plane: Vec<bool> = (0..(3 * self.size / 2).pow(2))
                    .map(|_| false)
                    .collect::<Vec<_>>();
                let extended = tiles.iter().map(|t| t.extend(rule)).collect::<Vec<_>>();
                let mut j = 0;
                for (ii, t) in extended.iter().enumerate() {
                    let i = ii % self.size;
                    for k in 0..9 {
                        plane[(j * self.size + i) * 9 + k] = t.0[k];
                    }
                    if i == self.size - 1 {
                        j += 1;
                    }
                }
                Some(Plane {
                    size: self.size / 2 * 3,
                    plane,
                })
            }
            Divided::By3(tiles) => {
                let mut plane: Vec<bool> = (0..(4 * self.size / 3).pow(2))
                    .map(|_| false)
                    .collect::<Vec<_>>();
                let extended = tiles.iter().map(|t| t.extend(rule)).collect::<Vec<_>>();
                let mut j = 0;
                for (ii, t) in extended.iter().enumerate() {
                    let i = ii % self.size;
                    for k in 0..16 {
                        plane[(j * self.size + i) * 16 + k] = t.0[k];
                    }
                    if i == self.size - 1 {
                        j += 1;
                    }
                }
                Some(Plane {
                    size: self.size / 3 * 4,
                    plane,
                })
            }
            Divided::None => None,
        }
    }
    fn count(&self) -> usize {
        self.plane.iter().filter(|b| **b).count()
    }
}

trait Block: Clone {
    type Extended;
    fn rotate_cw(&self) -> Self;
    fn flip_h(&self) -> Self;
    fn permutation(&self, index: usize) -> Self {
        assert!(index < 8);
        let mut p: Self = self.clone();
        for _ in 0..(index >> 1) {
            p = p.rotate_cw();
        }
        if 0 != index & 1 {
            p = p.flip_h();
        }
        p
    }
    fn extend(&self, rule: &Rule) -> Self::Extended;
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Plane2(Vec<bool>);

impl Block for Plane2 {
    type Extended = Plane3;
    fn rotate_cw(&self) -> Self {
        Plane2(vec![self.0[2], self.0[0], self.0[3], self.0[1]])
    }
    fn flip_h(&self) -> Self {
        Plane2(vec![self.0[1], self.0[0], self.0[3], self.0[2]])
    }
    fn extend(&self, rule: &Rule) -> Self::Extended {
        dbg!(&self);
        for (k, v) in rule.iter() {
            if *k == self.0 {
                return Plane3(v.clone());
            }
        }
        unreachable!()
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Plane3(Vec<bool>);

impl Block for Plane3 {
    type Extended = Plane4;
    fn rotate_cw(&self) -> Self {
        Plane3(vec![
            self.0[6], self.0[3], self.0[0], // first row
            self.0[7], self.0[4], self.0[1], // center row
            self.0[8], self.0[5], self.0[2], // last row
        ])
    }
    fn flip_h(&self) -> Self {
        Plane3(vec![
            self.0[2], self.0[1], self.0[0], // first row
            self.0[5], self.0[4], self.0[3], // center row
            self.0[8], self.0[7], self.0[6], // last row
        ])
    }
    fn extend(&self, rule: &Rule) -> Self::Extended {
        for (k, v) in rule.iter() {
            if *k == self.0 {
                // dbg!(&v);
                // println!("{:?}", Plane4(v.clone()));
                return Plane4(v.clone());
            }
        }
        unreachable!();
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Plane4(Vec<bool>);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(Vec<bool>, Vec<bool>)>,
    rule: Rule,
}

#[aoc(2017, 21)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^([.#/]+) => ([.#/]+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1]
                .chars()
                .filter(|c| *c != '/')
                .map(|c| c == '#')
                .collect::<Vec<_>>(),
            segment[2]
                .chars()
                .filter(|c| *c != '/')
                .map(|c| c == '#')
                .collect::<Vec<_>>(),
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        for l in self.line.iter() {
            // println!("{:?} => {:?}", l.0, l.1,);
            if l.0.len() == 4 {
                let p2 = Plane2(vec![l.0[0], l.0[1], l.0[2], l.0[3]]);
                for perm_index in 0..8 {
                    self.rule
                        .insert(p2.permutation(perm_index).0.to_vec(), l.1.clone());
                }
            } else {
                let p3 = Plane3(vec![
                    l.0[0], l.0[1], l.0[2], l.0[3], l.0[4], l.0[5], l.0[6], l.0[7], l.0[8],
                ]);
                for perm_index in 0..8 {
                    self.rule
                        .insert(p3.permutation(perm_index).0.to_vec(), l.1.clone());
                }
            }
        }
        dbg!(&self.rule.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut grid: Plane = Plane {
            size: 3,
            plane: vec![false, true, false, false, false, true, true, true, true],
        };
        for i in 0..5 {
            println!("loop: {}, size: {}:\n{:?}", i, grid.size, grid);
            grid = grid.extend(&self.rule).expect("something is wrong.");
            println!("{:?}", grid.plane);
        }
        grid.count()
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
