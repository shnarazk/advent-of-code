//! <https://adventofcode.com/2019/day/24>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
    },
    std::collections::HashSet,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
}

#[aoc(2019, 24)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c == '#').collect::<Vec<_>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(self.to_u32());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut visited: HashSet<u32> = HashSet::new();
        let mut state: u32 = self.to_u32();
        loop {
            // dump(state);
            let mut new_state: u32 = state;
            for i in 0..25 {
                let mut neighbors = 0;
                if 4 < i {
                    neighbors += (0 != (state & (1 << (i - 5)))) as u32;
                }
                if i < 20 {
                    neighbors += (0 != (state & (1 << (i + 5)))) as u32;
                }
                if 0 < i && i % 5 != 0 {
                    neighbors += (0 != (state & (1 << (i - 1)))) as u32;
                }
                if i < 24 && i % 5 != 4 {
                    neighbors += (0 != (state & (1 << (i + 1)))) as u32;
                }
                match (0 != state & (1 << i), neighbors) {
                    (true, n) if n != 1 => new_state &= !(1 << i),
                    (false, 1) | (false, 2) => new_state |= 1 << i,
                    _ => (),
                }
            }
            dbg!(state);
            if visited.contains(&new_state) {
                return new_state as usize;
            }
            visited.insert(new_state);
            state = new_state;
        }
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

impl Puzzle {
    fn to_u32(&self) -> u32 {
        let mut code: u32 = 0;
        let mut radix: u32 = 1;
        for l in self.line.iter() {
            for b in l.iter() {
                code += radix * (*b as u32);
                radix *= 2;
            }
        }
        code
    }
}

fn dump(state: u32) {
    for i in 0..25 {
        print!(
            "{}{}",
            if 0 != (state & (1 << i)) { '#' } else { '.' },
            if i % 5 == 4 { '\n' } else { ' ' },
        )
    }
}
