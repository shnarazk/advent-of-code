//! <https://adventofcode.com/2017/day/21>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
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
            if (i + 1) % self.size == 0 && i + 1 < self.plane.len() {
                let _ = writeln!(f);
            }
        }
        Ok(())
    }
}
impl Plane {
    fn divide(&self) -> Divided {
        if self.size % 2 == 0 {
            let mut result = Vec::new();
            let block_len = self.size / 2;
            let size = self.size;
            for index in 0..block_len.pow(2) {
                let j_start = (size * 2) * (index / block_len);
                let i_start = 2 * (index % block_len);
                let mut pack: Vec<bool> = vec![];
                for j in 0..2 {
                    for i in 0..2 {
                        pack.push(self.plane[j_start + j * size + i_start + i]);
                    }
                }
                result.push(Plane2(pack));
            }
            return Divided::By2(result);
        } else if self.size % 3 == 0 {
            let mut result = Vec::new();
            let block_len = self.size / 3;
            let size = self.size;
            for index in 0..block_len.pow(2) {
                let j_start = (size * 3) * (index / block_len);
                let i_start = 3 * (index % block_len);
                let mut pack: Vec<bool> = vec![];
                for j in 0..3 {
                    for i in 0..3 {
                        pack.push(self.plane[j_start + j * size + i_start + i]);
                    }
                }
                result.push(Plane3(pack));
            }
            return Divided::By3(result);
        }
        Divided::None
    }
    fn extend(&self, rule: &Rule) -> Option<Plane> {
        match self.divide() {
            Divided::By2(tiles) => {
                let block_len = self.size / 2;
                let size = self.size / 2 * 3;
                let extended = tiles.iter().map(|t| t.extend(rule)).collect::<Vec<_>>();
                let mut plane: Vec<bool> = (0..size.pow(2)).map(|_| false).collect::<Vec<_>>();
                for (index, t) in extended.iter().enumerate() {
                    // dbg!(index / block_len, index % block_len);
                    let j_start = (size * 3) * (index / block_len);
                    let i_start = 3 * (index % block_len);
                    // dbg!(j_start, i_start);
                    for j in 0..3 {
                        for i in 0..3 {
                            plane[j_start + j * size + i_start + i] = t.0[j * 3 + i];
                        }
                    }
                }
                Some(Plane { size, plane })
            }
            Divided::By3(tiles) => {
                let block_len = self.size / 3;
                let size = self.size / 3 * 4;
                let extended = tiles.iter().map(|t| t.extend(rule)).collect::<Vec<_>>();
                let mut plane: Vec<bool> = (0..size.pow(2)).map(|_| false).collect::<Vec<_>>();
                for (index, t) in extended.iter().enumerate() {
                    let j_start = (size * 4) * (index / block_len);
                    let i_start = 4 * (index % block_len);
                    for j in 0..4 {
                        for i in 0..4 {
                            plane[j_start + j * size + i_start + i] = t.0[j * 4 + i];
                        }
                    }
                }
                Some(Plane { size, plane })
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
        debug_assert!(index < 8);
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

#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Plane2(Vec<bool>);

impl std::fmt::Debug for Plane2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, b) in self.0.iter().enumerate() {
            let _ = write!(f, "{}", if *b { '#' } else { '.' });
            if (i + 1) % 2 == 0 && i < 3 {
                let _ = write!(f, "/");
            }
        }
        Ok(())
    }
}
impl Block for Plane2 {
    type Extended = Plane3;
    fn rotate_cw(&self) -> Self {
        Plane2(vec![self.0[2], self.0[0], self.0[3], self.0[1]])
    }
    fn flip_h(&self) -> Self {
        Plane2(vec![self.0[1], self.0[0], self.0[3], self.0[2]])
    }
    fn extend(&self, rule: &Rule) -> Self::Extended {
        // dbg!(&self);
        for (k, v) in rule.iter() {
            if *k == self.0 {
                return Plane3(v.clone());
            }
        }
        unreachable!()
    }
}

#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Plane3(Vec<bool>);

impl std::fmt::Debug for Plane3 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, b) in self.0.iter().enumerate() {
            let _ = write!(f, "{}", if *b { '#' } else { '.' });
            if (i + 1) % 3 == 0 && i < 8 {
                let _ = write!(f, "/");
            }
        }
        Ok(())
    }
}
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
    fn end_of_data(&mut self) {
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
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut grid: Plane = Plane {
            size: 3,
            plane: vec![false, true, false, false, false, true, true, true, true],
        };
        for _ in 0..5 {
            grid = grid.extend(&self.rule).expect("something is wrong.");
            // println!("loop: {}, size: {}:\n{:?}", i, grid.size, grid);
        }
        grid.count()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut grid: Plane = Plane {
            size: 3,
            plane: vec![false, true, false, false, false, true, true, true, true],
        };
        for _ in 0..18 {
            grid = grid.extend(&self.rule).expect("something is wrong.");
            // TODO: check multiple occurences of a block: we can reduce to a linear recursion.
        }
        grid.count()
    }
}
