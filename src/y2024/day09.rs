//! <https://adventofcode.com/2024/day/9>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser,
    },
    serde::Serialize,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<usize>,
    /// id to its length
    file_len: Vec<usize>,
    /// id to its length
    free_len: Vec<usize>,
}

#[aoc(2024, 9)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = parser::to_digits(input)?;
        for (i, x) in self.line.iter().enumerate() {
            if i % 2 == 0 {
                self.file_len.push(*x);
            } else {
                self.free_len.push(*x);
            }
        }
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let disc_len = self.line.iter().cloned().sum::<usize>();
        let mut disc_image: Vec<Option<u32>> = vec![None; disc_len];
        let mut p: usize = 0;
        for (i, n) in self.line.iter().enumerate() {
            let v = (i % 2 == 0).then_some(i as u32 / 2);
            for q in disc_image.iter_mut().skip(p).take(*n) {
                *q = v;
            }
            p += n;
        }
        let mut left: usize = 0;
        let mut right: usize = disc_image.len() - 1;
        'stop: while left < right {
            if disc_image[left].is_none() {
                while disc_image[right].is_none() {
                    if right <= left {
                        break 'stop;
                    }
                    right -= 1;
                }
                disc_image.swap(left, right);
            }
            left += 1;
        }
        disc_image
            .iter()
            .enumerate()
            .map(|(i, x)| x.map_or(0, |v| i * (v as usize)))
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut file_start: Vec<usize> = vec![0; self.file_len.len()];
        let mut free_start: Vec<usize> = vec![0; self.free_len.len()];
        let mut start = 0;
        for (i, &l) in self.line.iter().enumerate() {
            if i % 2 == 0 {
                file_start[i / 2] = start;
            } else {
                free_start[i / 2] = start;
            }
            start += l;
        }
        'next_file: for (id, &len) in self.file_len.iter().enumerate().rev() {
            let mut target = 0;
            while free_start[target] < file_start[id] {
                if len <= self.free_len[target] {
                    file_start[id] = free_start[target];
                    free_start[target] += len;
                    self.free_len[target] -= len;
                    continue 'next_file;
                }
                target += 1;
            }
        }
        self.file_len
            .iter()
            .enumerate()
            .map(|(id, &len)| (0..len).map(|i| id * (i + file_start[id])).sum::<usize>())
            .sum()
    }
}
