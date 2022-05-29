//! <https://adventofcode.com/2016/day/14>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    md5::{Digest, Md5},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<()>,
}

#[aoc(2016, 14)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut hasher = Md5::new();
        let mut count = 0;
        for i in 0.. {
            hasher.update(format!("wtnhxymk{i}"));
            let result = hasher.finalize_reset();
            if result[0] == 0 && result[1] == 0 && result[2] >> 4 == 0 {
                println!("{:x}", result);
                count += 1;
                if 8 <= count {
                    break;
                }
            }
        }
        0
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
                println!("{:x}", result);
                ans[result[2] as usize] = Some(result[3] >> 4);
                count += 1;
                if 8 <= count {
                    break;
                }
            }
        }
        println!("{:?}", ans);
        0
    }
}
