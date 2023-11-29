//! <https://adventofcode.com/2017/day/14>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: String,
}

#[aoc(2017, 14)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block.trim().to_string();
        Ok(())
    }
    fn wrap_up(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut count: usize = 0;
        for i in 0..128 {
            let key = format!("{}-{i}", self.line);
            let val = self.knot_hash(key);
            count += val.iter().map(|v| v.count_ones()).sum::<u32>() as usize;
        }
        count
    }
    fn part2(&mut self) -> Self::Output2 {
        type Location = (isize, isize);
        let mut map: HashMap<Location, usize> = HashMap::new();
        for j in 0..128 {
            let key = format!("{}-{j}", self.line);
            let val = self.knot_hash(key);
            for (ii, v) in val.iter().enumerate() {
                let offset = ii * 8;
                for i in (0..8).filter(|i| 0 != v & (1 << (7 - i))) {
                    map.insert((j as isize, (i + offset) as isize), 0);
                }
            }
        }
        let mut regions = 0;
        for j in 0..128_isize {
            for i in 0..128_isize {
                let pos = (j, i);
                if map.get(&pos) == Some(&0) {
                    regions += 1;
                    *map.entry(pos).or_insert(0) = regions;
                    let mut to_visit: Vec<Location> = vec![pos];
                    while let Some(p) = to_visit.pop() {
                        for offset in [(-1_isize, 0_isize), (0, 1), (1, 0), (0, -1)] {
                            let neighbor = (p.0 + offset.0, p.1 + offset.1);
                            if map.get(&neighbor) == Some(&0) {
                                to_visit.push(neighbor);
                                *map.entry(neighbor).or_insert(0) = regions;
                            }
                        }
                    }
                }
            }
        }
        regions
    }
}

impl Puzzle {
    fn knot_hash(&self, key: impl AsRef<str>) -> Vec<u8> {
        let m: usize = 256;
        let mut list: Vec<u8> = (0..m).map(|d| d as u8).collect::<Vec<u8>>();
        let lengths: Vec<usize> = {
            let mut list: Vec<usize> = key.as_ref().chars().map(|c| c as usize).collect::<Vec<_>>();
            let mut postfix = vec![17, 31, 73, 47, 23];
            list.append(&mut postfix);
            list
        };

        let mut current_position = 0;
        let mut skip_size = 0;
        for _ in 0..64 {
            for length in lengths.iter() {
                for j in 0..*length / 2 {
                    list.swap(
                        (current_position + j) % m,
                        (current_position + *length - j - 1) % m,
                    );
                }
                current_position += length + skip_size;
                current_position %= m;
                skip_size += 1;
            }
        }
        let mut result: Vec<u8> = Vec::new();
        let mut working: u8 = 0;
        for (i, c) in list.iter().enumerate() {
            match i % 16 {
                0 => working = *c,
                15 => result.push(working ^ *c),
                _ => working ^= *c,
            }
        }
        result
    }
}
