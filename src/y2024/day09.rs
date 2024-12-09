//! <https://adventofcode.com/2024/day/9>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser,
    },
    serde::Serialize,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<usize>,
    // id to its length
    file: Vec<usize>,
    // id to its length
    free: Vec<usize>,
}

#[aoc(2024, 9)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parser::to_digits(input.as_str())?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for (i, x) in self.line.iter().enumerate() {
            if i % 2 == 0 {
                self.file.push(*x);
            } else {
                self.free.push(*x);
            }
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        let len = self.line.iter().cloned().sum::<usize>();
        let mut tmp: Vec<Option<u32>> = vec![None; len];
        let mut p: usize = 0;
        for (i, n) in self.line.iter().enumerate() {
            let v = (i % 2 == 0).then_some(i as u32 / 2);
            for q in tmp.iter_mut().skip(p).take(*n) {
                *q = v;
            }
            p += n;
        }
        let mut left: usize = 0;
        let mut right: usize = tmp.len() - 1;
        'stop: while left < right {
            if tmp[left].is_none() {
                while tmp[right].is_none() {
                    if right <= left {
                        break 'stop;
                    }
                    right -= 1;
                }
                tmp.swap(left, right);
            }
            left += 1;
        }
        tmp.iter()
            .enumerate()
            .map(|(i, x)| x.map_or(0, |v| i * (v as usize)))
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let len = self.line.iter().cloned().sum::<usize>();
        let mut tmp: Vec<Option<u32>> = vec![None; len];
        let mut start_at: Vec<usize> = vec![0; self.file.len()];
        let mut p: usize = 0;
        for (i, n) in self.line.iter().enumerate() {
            if i % 2 == 0 {
                start_at[i / 2] = p;
            }
            let v = (i % 2 == 0).then_some(i as u32 / 2);
            for q in tmp.iter_mut().skip(p).take(*n) {
                *q = v;
            }
            p += n;
        }
        'next_file: for (id, &ln) in self.file.iter().enumerate().rev() {
            let mut left: Option<usize> = None;
            let mut right = 0;
            while right < start_at[id] {
                if let Some(l) = tmp[right] {
                    left = None;
                    right += self.file[l as usize];
                } else {
                    if left.is_none() {
                        left = Some(right);
                    }
                    if let Some(l) = left {
                        if ln == right - l + 1 {
                            for i in tmp.iter_mut().skip(l).take(ln) {
                                *i = Some(id as u32);
                            }
                            for i in tmp.iter_mut().skip(start_at[id]).take(self.file[id]) {
                                *i = None;
                            }
                            continue 'next_file;
                        }
                    }
                    right += 1;
                }
            }
        }
        tmp.iter()
            .enumerate()
            .map(|(i, x)| x.map_or(0, |v| i * (v as usize)))
            .sum()
    }
}
