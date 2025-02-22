//! <https://adventofcode.com/2022/day/25>
use crate::framework::{AdventOfCode, ParseError, aoc_at};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<isize>>,
}

#[aoc_at(2022, 25)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = ();
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|l| {
                l.chars()
                    .map(|c| match c {
                        '-' => -1,
                        '=' => -2,
                        '0' | '1' | '2' | '3' => c as isize - '0' as isize,
                        _ => unreachable!(),
                    })
                    .collect::<Vec<isize>>()
            })
            .collect();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut sum: usize = self
            .line
            .iter()
            .map(|n| {
                let v = n
                    .iter()
                    .rev()
                    .enumerate()
                    .fold(0, |acc, (i, k)| acc + k * 5_isize.pow(i as u32))
                    as usize;
                v
            })
            .sum();
        let mut buffer: Vec<char> = Vec::new();
        while 0 < sum {
            let digit = sum % 5;
            sum /= 5;
            let ch = match digit {
                0..=2 => (b'0' + digit as u8) as char,
                3 => {
                    sum += 1;
                    '='
                }
                4 => {
                    sum += 1;
                    '-'
                }
                _ => unreachable!(),
            };
            buffer.push(ch);
        }
        buffer.reverse();
        buffer.iter().collect::<String>()
    }
    fn part2(&mut self) -> Self::Output2 {}
}
