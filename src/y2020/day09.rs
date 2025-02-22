//! <https://adventofcode.com/2020/day/9>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashSet,
};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    vec: Vec<usize>,
    len: usize,
}

#[aoc(2020, 9)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            self.vec.push(l.parse::<usize>()?);
        }
        self.len = if 100 < self.vec.len() { 25 } else { 5 };
        Ok(())
    }
    fn part1(&mut self) -> usize {
        let len = self.len;
        let mut set: HashSet<usize> = HashSet::new();
        for n in &self.vec[..len] {
            set.insert(*n);
        }
        for (i, n) in self.vec.iter().enumerate().skip(len) {
            let out = self.vec[i - len];
            let mut found = false;
            for k in &set {
                if 2 * *k < *n && set.contains(&(*n - *k)) {
                    found = true;
                    break;
                }
            }
            if found {
                set.remove(&out);
                assert!(!set.contains(&out));
                if !set.insert(*n) {
                    panic!("this requires HashMap");
                }
                assert!(set.contains(n));
            } else {
                return *n;
            }
        }
        0
    }
    fn part2(&mut self) -> usize {
        let len = self.vec.len();
        let magic_number = self.part1();
        'next: for start in 0..len {
            let mut sum = 0;
            for i in start..len {
                sum += self.vec[i];
                if sum == magic_number {
                    let mn = *self.vec[start..i].iter().min().unwrap();
                    let mx = *self.vec[start..i].iter().max().unwrap();
                    return mn + mx;
                }
                if magic_number < sum {
                    continue 'next;
                }
            }
        }
        0
    }
}
