//! <https://adventofcode.com/2016/day/05>
use {
    crate::framework::{aoc_at, AdventOfCode, ParseError},
    md5::{Digest, Md5},
    std::fmt::Write,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<()>,
}

#[aoc_at(2016, 5)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = String;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut ans: Vec<u8> = Vec::new();
        let mut hasher = Md5::new();
        let mut count = 0;
        for i in 0.. {
            hasher.update(format!("wtnhxymk{i}"));
            let result = hasher.finalize_reset();
            if result[0] == 0 && result[1] == 0 && result[2] >> 4 == 0 {
                ans.push(result[2]);
                count += 1;
                if 8 <= count {
                    break;
                }
            }
        }
        ans.iter().fold(String::new(), |mut s, n| {
            write!(s, "{:x}", n).map(|_| s).unwrap()
        })
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut hasher = Md5::new();
        let mut count = 0;
        let mut ans: [Option<u8>; 8] = [None; 8];
        for i in 0.. {
            hasher.update(format!("wtnhxymk{i}"));
            let result = hasher.finalize_reset();
            if result[0] == 0
                && result[1] == 0
                && result[2] < 8
                && ans[result[2] as usize].is_none()
            {
                ans[result[2] as usize] = Some(result[3] >> 4);
                count += 1;
                if 8 <= count {
                    break;
                }
            }
        }
        ans.iter().fold(String::new(), |mut s, n| {
            write!(s, "{:x}", n.unwrap()).map(|_| s).unwrap()
        })
    }
}
