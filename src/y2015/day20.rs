//! <https://adventofcode.com/2015/day/20>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {}

#[aoc(2015, 20)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        const INPUT: usize = 34000000;
        for n in 2..INPUT {
            let nq = (n as f64).sqrt().floor() as usize;
            let mut sum = 1 + n;
            for k in 2..nq {
                if n % k == 0 {
                    sum += k;
                    sum += n / k;
                }
            }
            if nq * nq == n {
                sum += nq;
            }
            if INPUT <= sum * 10 {
                return n;
            }
            // if n % 10000 == 0 {
            //     dbg!(n, sum);
            // }
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        const INPUT: usize = 34000000;
        for n in 2..INPUT {
            let nq = (n as f64).sqrt().floor() as usize;
            let mut sum = 0;
            for k in 1..=nq {
                if n % k == 0 {
                    if n / k <= 50 {
                        sum += k;
                    }
                    if k <= 50 {
                        sum += n / k;
                    }
                }
            }
            if nq * nq == n && nq <= 50 {
                sum += nq;
            }
            if INPUT <= sum * 11 {
                return n;
            }
            // if n % 10000 == 0 {
            //     dbg!(n, sum);
            // }
        }
        0
    }
}
