//! <https://adventofcode.com/2016/day/02>
use {
    crate::framework::{AdventOfCode, ParseError, aoc_at},
    std::fmt::Write,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
}

#[aoc_at(2016, 2)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = String;
    fn prepare(&mut self, s: &str) -> Result<(), ParseError> {
        self.line = s.lines().map(|l| l.chars().collect()).collect();
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut key: Vec<usize> = Vec::new();
        let mut x: isize = 0;
        let mut y: isize = 0;
        for v in self.line.iter() {
            for ch in v.iter() {
                match *ch {
                    'U' => y = (y - 1).clamp(-1, 1),
                    'D' => y = (y + 1).clamp(-1, 1),
                    'L' => x = (x - 1).clamp(-1, 1),
                    'R' => x = (x + 1).clamp(-1, 1),
                    _ => unreachable!(),
                }
            }
            key.push((3 * (y + 1) + (x + 1) + 1) as usize);
        }
        key.iter().fold(String::new(), |mut s, n| {
            write!(s, "{n}").map(|_| s).unwrap()
        })
    }
    fn part2(&mut self) -> Self::Output2 {
        fn to_char(y: isize, x: isize) -> char {
            match (y, x) {
                (-2, 0) => '1',
                (-1, -1) => '2',
                (-1, 0) => '3',
                (-1, 1) => '4',
                (0, -2) => '5',
                (0, -1) => '6',
                (0, 0) => '7',
                (0, 1) => '8',
                (0, 2) => '9',
                (1, -1) => 'A',
                (1, 0) => 'B',
                (1, 1) => 'C',
                (2, 0) => 'D',
                _ => unreachable!(),
            }
        }
        fn clamp_2d(val: isize, range: isize) -> isize {
            let r = 2 - range.abs();
            val.clamp(-r, r)
        }
        let mut key: Vec<char> = Vec::new();
        let mut x: isize = -2;
        let mut y: isize = 0;
        for v in self.line.iter() {
            for ch in v.iter() {
                match *ch {
                    'U' => y = clamp_2d(y - 1, x),
                    'D' => y = clamp_2d(y + 1, x),
                    'L' => x = clamp_2d(x - 1, y),
                    'R' => x = clamp_2d(x + 1, y),
                    _ => unreachable!(),
                }
            }
            key.push(to_char(y, x));
        }
        key.iter().fold(String::new(), |mut s, n| {
            write!(s, "{n}").map(|_| s).unwrap()
        })
    }
}
