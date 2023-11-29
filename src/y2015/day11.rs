//! <https://adventofcode.com/2015/day/11>
use crate::framework::{aoc_at, AdventOfCode, ParseError};

fn valid(vec: &[char]) -> bool {
    vec.windows(3)
        .any(|c3| c3[0] as u8 + 1 == c3[1] as u8 && c3[0] as u8 + 2 == c3[2] as u8)
        && vec.iter().all(|c| !['i', 'o', 'l'].contains(c))
        && vec
            .windows(2)
            .enumerate()
            .any(|(i, c2)| c2[0] == c2[1] && vec[i + 2..].windows(2).any(|d2| d2[0] == d2[1]))
}

fn increment(vec: &mut [char]) {
    let mut target = vec.len() - 1;
    let mut add = |n: usize| -> bool {
        if vec[n] == 'z' {
            vec[n] = 'a';
            true
        } else {
            vec[n] = (vec[n] as u8 + 1) as char;
            false
        }
    };
    while add(target) {
        assert!(0 < target);
        target -= 1;
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
}

#[aoc_at(2015, 11)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = String;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.chars().collect::<Vec<char>>());
        Ok(())
    }
    fn wrap_up(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut result: String = "".to_string();
        for l in self.line.iter() {
            let mut p = l.clone();
            increment(&mut p);
            while !valid(&p) {
                increment(&mut p);
            }
            result = p.iter().collect::<String>();
            println!("{} => {}", l.iter().collect::<String>(), result);
        }
        result
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut next_one = self.part1().chars().collect::<Vec<char>>();
        increment(&mut next_one);
        while !valid(&next_one) {
            increment(&mut next_one);
        }
        return next_one.iter().collect::<String>();
    }
}
