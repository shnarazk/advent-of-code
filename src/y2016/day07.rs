//! <https://adventofcode.com/2016/day/07>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashSet,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
}

#[aoc(2016, 7)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, s: String) -> Result<String, ParseError> {
        self.line = s
            .lines()
            .map(|l| l.chars().map(|c| c as u8).collect())
            .collect();
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .filter(|l| {
                let mut certified = false;
                let mut in_bracket = false;
                let mut after_mode_change = 0;
                for (i, c) in l.iter().enumerate() {
                    if in_bracket {
                        if *c == b']' {
                            in_bracket = false;
                            after_mode_change = 3;
                            continue;
                        }
                        if 0 < after_mode_change {
                            after_mode_change -= 1;
                            continue;
                        }
                        if i < 3 {
                            continue;
                        }
                        if *c != l[i - 1] && l[i - 1] == l[i - 2] && *c == l[i - 3] {
                            certified = false;
                            break;
                        }
                    } else {
                        if *c == b'[' {
                            in_bracket = true;
                            after_mode_change = 3;
                            continue;
                        }
                        if 0 < after_mode_change {
                            after_mode_change -= 1;
                            continue;
                        }
                        if i < 3 {
                            continue;
                        }
                        if *c != l[i - 1] && l[i - 1] == l[i - 2] && *c == l[i - 3] {
                            certified = true;
                        }
                    }
                }
                certified
            })
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .filter(|l| {
                let mut in_bracket = false;
                let mut after_mode_change = 0;
                let mut aba: HashSet<(u8, u8)> = HashSet::new();
                let mut bab: HashSet<(u8, u8)> = HashSet::new();
                for (i, c) in l.iter().enumerate() {
                    if in_bracket {
                        if *c == b']' {
                            in_bracket = false;
                            after_mode_change = 2;
                            continue;
                        }
                        if 0 < after_mode_change {
                            after_mode_change -= 1;
                            continue;
                        }
                        if i < 2 {
                            continue;
                        }
                        if *c != l[i - 1] && *c == l[i - 2] {
                            bab.insert((*c, l[i - 1]));
                        }
                    } else {
                        if *c == b'[' {
                            in_bracket = true;
                            after_mode_change = 2;
                            continue;
                        }
                        if 0 < after_mode_change {
                            after_mode_change -= 1;
                            continue;
                        }
                        if i < 2 {
                            continue;
                        }
                        if *c != l[i - 1] && *c == l[i - 2] {
                            aba.insert((*c, l[i - 1]));
                        }
                    }
                }
                aba.iter().any(|(p, q)| bab.contains(&(*q, *p)))
            })
            .count()
    }
}
