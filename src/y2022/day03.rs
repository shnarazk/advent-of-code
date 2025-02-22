//! <https://adventofcode.com/2022/day/3>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(Vec<u8>, Vec<u8>)>,
}

#[aoc(2022, 3)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|l| {
                let v = l.trim().chars().map(|c| c as u8).collect::<Vec<_>>();
                let len = v.len();
                let (left, right) = v.split_at(len / 2);
                (left.to_vec(), right.to_vec())
            })
            .collect::<Vec<_>>();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut count = 0;
        for l in self.line.iter() {
            for c in l.0.iter() {
                if l.1.contains(c) {
                    count += if *c <= b'Z' {
                        (*c - b'A') as usize + 27
                    } else {
                        (*c - b'a') as usize + 1
                    };
                    break;
                }
            }
        }
        count
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut count = 0;
        let mut map: HashMap<u8, usize> = HashMap::new();
        for (i, l) in self.line.iter().enumerate() {
            for c in l.0.iter() {
                *map.entry(*c).or_insert(0) |= 1 << (i % 3);
            }
            for c in l.1.iter() {
                *map.entry(*c).or_insert(0) |= 1 << (i % 3);
            }
            if i % 3 == 2 {
                for (c, n) in map.iter() {
                    if *n == 7 {
                        // dbg!(*c as usize);
                        count += if *c <= b'Z' {
                            (*c - b'A') as usize + 27
                        } else {
                            (*c - b'a') as usize + 1
                        };
                        break;
                    }
                }
                map.clear();
            }
        }
        count
    }
}
