//! <https://adventofcode.com/2020/day/5>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, PartialEq)]
pub struct Puzzle {
    seats: [bool; 128 * 8 + 1],
    max_sid: usize,
}

impl Default for Puzzle {
    fn default() -> Self {
        Puzzle {
            seats: [false; 128 * 8 + 1],
            max_sid: 0,
        }
    }
}

#[aoc(2020, 5)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            let chs = l.chars().collect::<Vec<char>>();
            let row = chs[..7]
                .iter()
                .map(|c| (*c == 'B') as usize)
                .fold(0, |t, n| t * 2 + n);
            let col = chs[7..]
                .iter()
                .map(|c| (*c == 'R') as usize)
                .fold(0, |t, n| t * 2 + n);
            let sid = row * 8 + col;

            self.seats[sid] = true;
            if self.max_sid < sid {
                self.max_sid = sid;
            }
        }
        Ok(())
    }
    fn part1(&mut self) -> usize {
        self.max_sid
    }
    fn part2(&mut self) -> usize {
        for (i, e) in self.seats.iter().enumerate() {
            if !*e && 7 < i && i < 126 * 8 && self.seats[i - 1] && self.seats[i + 1] {
                return i;
            }
        }
        0
    }
}
