//! <https://adventofcode.com/2020/day/6>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    dic: Vec<(usize, HashMap<char, usize>)>,
}

#[aoc(2020, 6)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        for block in input.split("\n\n").filter(|b| !b.is_empty()) {
            let mut dic: HashMap<char, usize> = HashMap::new();
            let n = block.lines().count();
            for ch in block.chars() {
                if ch.is_ascii_lowercase() {
                    *dic.entry(ch).or_insert(0) += 1;
                }
            }
            self.dic.push((n, dic));
        }
        Self::parsed()
    }
    fn part1(&mut self) -> usize {
        self.dic.iter().map(|(_, h)| h.len()).sum()
    }
    fn part2(&mut self) -> usize {
        self.dic
            .iter()
            .map(|(n, h)| h.values().filter(|m| n == *m).count())
            .sum()
    }
}
