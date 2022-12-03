//! <https://adventofcode.com/2022/day/3>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(Vec<u8>, Vec<u8>)>,
}

#[aoc(2022, 3)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let v = block.chars().map(|c| c as u8).collect::<Vec<u8>>();
        let len = v.len();
        self.line
            .push((v[0..len / 2].to_vec(), v[len / 2..len].to_vec()));
        // println!(
        //     "{}({}) => {}, {}",
        //     block,
        //     len,
        //     v[0..len / 2].iter().map(|c| *c as char).collect::<String>(),
        //     v[len / 2..len]
        //         .iter()
        //         .map(|c| *c as char)
        //         .collect::<String>(),
        // );
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
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
