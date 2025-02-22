//! <https://adventofcode.com/2018/day/2>
use {
    crate::framework::{AdventOfCode, ParseError, aoc_at},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
}

#[aoc_at(2018, 2)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|l| l.chars().map(|c| c as u8).collect::<Vec<_>>())
            .collect();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut twice: usize = 0;
        let mut thrice: usize = 0;
        for w in self.line.iter() {
            let mut count: HashMap<u8, usize> = HashMap::new();
            for c in w.iter() {
                *count.entry(*c).or_insert(0) += 1;
            }
            twice += count.values().any(|c| *c == 2) as usize;
            thrice += count.values().any(|c| *c == 3) as usize;
        }
        twice * thrice
    }
    fn part2(&mut self) -> Self::Output2 {
        for (j, word1) in self.line.iter().enumerate() {
            for word2 in self.line[j + 1..].iter() {
                let mut ndiff: usize = 0;
                let mut index: usize = 0;
                for (i, (c1, c2)) in word1.iter().zip(word2.iter()).enumerate() {
                    if c1 != c2 {
                        index = i;
                        ndiff += 1;
                    }
                }
                if ndiff == 1 {
                    return word1
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != index)
                        .map(|(_, c)| *c as char)
                        .collect::<String>();
                }
            }
        }
        unreachable!()
    }
}
