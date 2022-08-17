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

enum Divided {
    By2(Vec<Plane2>),
    By3(Vec<Plane3>),
    None,
}
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Plane {
    size: usize,
    plane: Vec<bool>,
}

impl Plane {
    fn divide(&self) -> Divided {
        if self.size % 2 == 0 {
            let mut result = Vec::new();
            for index in 0..(self.size / 2).pow(2) {
                let j_start = index / (self.size / 2);
                let i_start = index % (self.size / 2);
                let mut pack: Vec<bool> = Vec::new();
                for j in j_start..(j_start + 2) {
                    for i in i_start..(i_start + 2) {
                        pack.push(self.plane[j * self.size + i]);
                    }
                }
                result.push(Plane2([pack[0], pack[1], pack[2], pack[3]]));
            }
            return Divided::By2(result);
        } else if self.size % 3 == 0 {
            let mut result = Vec::new();
            for index in 0..(self.size / 3).pow(2) {
                let j_start = index / (self.size / 3);
                let i_start = index % (self.size / 3);
                let mut pack: Vec<bool> = Vec::new();
                for j in j_start..(j_start + 3) {
                    for i in i_start..(i_start + 3) {
                        pack.push(self.plane[j * self.size + i]);
                    }
                }
                result.push(Plane3([
                    pack[0], pack[1], pack[2], pack[3], pack[4], pack[5], pack[6], pack[7], pack[8],
                ]));
            }
            return Divided::By3(result);
        }
        Divided::None
    }
    fn extend(&self) -> Option<Plane> {
        match self.divide() {
            Divided::By2(v) => {}
            Divided::By3(v) => {}
            Divided::None => {
                return None;
            }
        }
        todo!()
    }
}

trait Block: Clone {
    fn rotate_cw(&self) -> Self;
    fn flip_h(&self) -> Self;
    fn permutations(&self, index: usize) -> Self {
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
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Plane2([bool; 4]);

impl Block for Plane2 {
    fn rotate_cw(&self) -> Self {
        Plane2([self.0[2], self.0[0], self.0[3], self.0[1]])
    }
    fn flip_h(&self) -> Self {
        Plane2([self.0[1], self.0[0], self.0[3], self.0[2]])
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Plane3([bool; 9]);

impl Block for Plane3 {
    fn rotate_cw(&self) -> Self {
        Plane3([
            self.0[6], self.0[3], self.0[0], // first row
            self.0[7], self.0[4], self.0[1], // center row
            self.0[8], self.0[5], self.0[2], // last row
        ])
    }
    fn flip_h(&self) -> Self {
        Plane3([
            self.0[2], self.0[1], self.0[0], // first row
            self.0[5], self.0[4], self.0[3], // center row
            self.0[8], self.0[7], self.0[6], // last row
        ])
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(Vec<u8>, Vec<u8>)>,
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
                .map(|c| c as u8)
                .collect::<Vec<_>>(),
            segment[2]
                .chars()
                .filter(|c| *c != '/')
                .map(|c| c as u8)
                .collect::<Vec<_>>(),
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        for l in self.line.iter() {
            println!(
                "{:?} => {:?}",
                l.0.iter().map(|c| *c as char).collect::<String>(),
                l.1.iter().map(|c| *c as char).collect::<String>(),
            );
        }
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}
