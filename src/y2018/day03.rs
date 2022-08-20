//! <https://adventofcode.com/2018/day/3>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        regex,
    },
    std::collections::{HashMap, HashSet},
};

type Dim2 = (usize, usize);

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Claim {
    id: usize,
    left: usize,
    top: usize,
    width: usize,
    height: usize,
}
#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Claim>,
}

#[aoc(2018, 3)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // #50 @ 718,864: 26x16
        let parser = regex!(r"^#(\d+) @ (\d+),(\d+): (\d+)x(\d+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push(Claim {
            id: segment[1].parse::<usize>()?,
            left: segment[2].parse::<usize>()?,
            top: segment[3].parse::<usize>()?,
            width: segment[4].parse::<usize>()?,
            height: segment[5].parse::<usize>()?,
        });
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut used: HashMap<Dim2, usize> = HashMap::new();
        for c in self.line.iter() {
            for j in (c.top..).take(c.height) {
                for i in (c.left..).take(c.width) {
                    *used.entry((j, i)).or_insert(0) += 1;
                }
            }
        }
        used.values().filter(|&&n| 1 < n).count()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut used: HashMap<Dim2, usize> = HashMap::new();
        let mut duplicated: HashSet<usize> = HashSet::new();
        for c in self.line.iter() {
            let mut dup = false;
            for j in (c.top..).take(c.height) {
                for i in (c.left..).take(c.width) {
                    if let Some(d) = used.get(&(j, i)) {
                        duplicated.insert(*d);
                        dup = true;
                    } else {
                        used.insert((j, i), c.id);
                    }
                }
            }
            if dup {
                duplicated.insert(c.id);
            }
        }
        for id in self.line.iter().map(|c| c.id) {
            if !duplicated.contains(&id) {
                return id;
            }
        }
        unreachable!();
    }
}
