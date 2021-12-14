//! <https://adventofcode.com/2020/day/5>
use crate::y2020::traits::{Description, ProblemSolver};

pub fn day05(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

#[derive(Debug, PartialEq)]
struct Setting {
    seats: [bool; 128 * 8 + 1],
    max_sid: usize,
}

impl ProblemSolver<usize, usize, usize> for Setting {
    const YEAR: usize = 2020;
    const DAY: usize = 5;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Setting {
            seats: [false; 128 * 8 + 1],
            max_sid: 0,
        }
    }
    fn insert(&mut self, n: usize) {
        self.seats[n] = true;
        if self.max_sid < n {
            self.max_sid = n;
        }
    }
    fn parse(desc: Description) -> Self {
        let mut s = Setting::default();

        if let Some(buffer) = Self::load(desc) {
            for code in buffer.split(Self::DELIMITER) {
                if code.is_empty() {
                    break;
                }
                let (row_code, col_code) = code.split_at(7);
                let row = row_code
                    .chars()
                    .map(|c| (c == 'B') as usize)
                    .collect::<Vec<_>>();
                let col = col_code
                    .chars()
                    .map(|c| (c == 'R') as usize)
                    .collect::<Vec<_>>();
                let r = row.iter().fold(0, |t, n| t * 2 + n);
                let c = col.iter().fold(0, |t, n| t * 2 + n);
                let sid = r * 8 + c;
                s.insert(sid);
            }
        }
        s
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
