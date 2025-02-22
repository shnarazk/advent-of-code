//! <https://adventofcode.com/2022/day/6>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashSet,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
}

#[aoc(2022, 6)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input.lines().map(|l| l.chars().collect()).collect();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|l| {
                let mut index = 0;
                for (i, chank) in l.windows(4).enumerate() {
                    if !chank[1..4].contains(&chank[0])
                        && !chank[2..4].contains(&chank[1])
                        && !chank[3..4].contains(&chank[2])
                    {
                        index = i + 4;
                        break;
                    }
                }
                index
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let size = 14;
        self.line
            .iter()
            .map(|l| {
                let mut index = 0;
                'next_chank: for (i, chank) in l.windows(size).enumerate() {
                    let mut set: HashSet<char> = HashSet::new();
                    for c in chank.iter() {
                        if set.contains(c) {
                            continue 'next_chank;
                        }
                        set.insert(*c);
                    }
                    index = i + size;
                    break;
                }
                index
            })
            .sum()
    }
}
