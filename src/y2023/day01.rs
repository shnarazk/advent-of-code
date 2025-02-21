//! <https://adventofcode.com/2023/day/1>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    table: [usize; 256],
    subst: Vec<Vec<u8>>,
    sum1: usize,
    sum2: usize,
}

impl Default for Puzzle {
    fn default() -> Self {
        let mut table = [0usize; 256];
        for i in 1..=9 {
            table[b'0' as usize + i] = i;
        }
        for c in [b'e', b'f', b'n', b'o', b's', b't'] {
            table[c as usize] = 10;
        }
        let subst = vec![
            b"one".to_vec(),
            b"two".to_vec(),
            b"three".to_vec(),
            b"four".to_vec(),
            b"five".to_vec(),
            b"six".to_vec(),
            b"seven".to_vec(),
            b"eight".to_vec(),
            b"nine".to_vec(),
        ];
        Puzzle {
            table,
            subst,
            sum1: 0,
            sum2: 0,
        }
    }
}

#[aoc(2023, 1)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            let b = l.bytes().collect::<Vec<_>>();
            let len = b.len();
            for dir in [0, 1] {
                let scale = 10 - dir * 9;
                let mut not_found = true;
                for ii in 0..len {
                    let i = if dir == 1 { len - ii - 1 } else { ii };
                    let mut value = self.table[b[i] as usize];
                    if value == 0 {
                        continue;
                    }
                    if value < 10 {
                        value *= scale;
                        if not_found {
                            self.sum2 += value;
                        }
                        self.sum1 += value;
                        break;
                    }
                    if not_found {
                        for (j, r) in self.subst.iter().enumerate() {
                            if b[i..].starts_with(r) {
                                self.sum2 += scale * (j + 1);
                                not_found = false;
                                break;
                            }
                        }
                    }
                }
            }
        }
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.sum1
    }
    fn part2(&mut self) -> Self::Output2 {
        self.sum2
    }
}
