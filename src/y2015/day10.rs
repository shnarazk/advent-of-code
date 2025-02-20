//! <https://adventofcode.com/2015/day/10>
use crate::framework::{aoc, AdventOfCode, ParseError};

fn formatter1(mut vec: &[usize]) -> Vec<usize> {
    let mut v = Vec::new();
    while !vec.is_empty() {
        let n = vec[0];
        let mut nrepeat = 0;
        for (i, x) in vec.iter().enumerate() {
            if *x == n {
                nrepeat = i;
            } else {
                break;
            }
        }
        nrepeat += 1;
        v.push(nrepeat);
        v.push(n);
        vec = &vec[nrepeat..];
    }
    v
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<usize>,
}

#[aoc(2015, 10)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, s: &str) -> Result<(), ParseError> {
        let mut n = s.trim().parse::<usize>()?;
        while 0 < n {
            self.line.push(n % 10);
            n /= 10;
        }
        self.line.reverse();
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.iterate(self.line.clone(), 40)
    }
    fn part2(&mut self) -> Self::Output2 {
        self.iterate(self.line.clone(), 50)
    }
}

impl Puzzle {
    fn iterate(&self, n: Vec<usize>, upto: usize) -> usize {
        (0..upto)
            .fold(n, |n, _| formatter1(&n))
            .iter()
            .map(|n| n.ilog10() as usize + 1)
            .sum::<usize>()
    }
}
