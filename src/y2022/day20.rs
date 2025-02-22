//! <https://adventofcode.com/2022/day/20>
use {
    crate::framework::{AdventOfCode, ParseError, aoc_at},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
    len: usize,
    index_zero: usize,
    debug: bool,
}

#[aoc_at(2022, 20)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            self.line.push(l.parse::<isize>()?);
        }
        self.len = self.line.len();
        self.index_zero = self
            .line
            .iter()
            .enumerate()
            .find(|(_, i)| **i == 0)
            .expect("")
            .0;
        let mut count: HashMap<isize, usize> = HashMap::new();
        for n in self.line.iter() {
            *count.entry(*n).or_insert(0) += 1;
        }
        // assert!(count.values().all(|c| *c == 1));
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut next: Vec<usize> = (0..self.len)
            .map(|i| (i + 1) % self.len)
            .collect::<Vec<usize>>();
        let mut prev: Vec<usize> = (0..self.len)
            .map(|i| (i + self.len - 1) % self.len)
            .collect::<Vec<usize>>();
        // self.print(&next);
        for n in 0..self.line.len() {
            self.shift(&mut next, &mut prev, n);
            // self.print(&next);
            let mut check = next.clone();
            check.sort();
            let cal = (0..self.len).collect::<Vec<usize>>();
            debug_assert_eq!(check, cal);
            debug_assert!(self.is_sound(&next), "{n}");
        }
        // self.print(&next);
        self.value(&next)
    }
    fn part2(&mut self) -> Self::Output2 {
        let key = 811589153;
        for n in self.line.iter_mut() {
            *n *= key;
        }
        let mut next: Vec<usize> = (0..self.len)
            .map(|i| (i + 1) % self.len)
            .collect::<Vec<usize>>();
        let mut prev: Vec<usize> = (0..self.len)
            .map(|i| (i + self.len - 1) % self.len)
            .collect::<Vec<usize>>();
        // self.trace(&next);
        for s in 0..10 {
            for n in 0..self.line.len() {
                self.debug = s == 5;
                self.shift(&mut next, &mut prev, n);
            }
            // self.trace(&next);
        }
        self.value(&next)
    }
}

impl Puzzle {
    fn shift(&self, next: &mut [usize], prev: &mut [usize], i: usize) {
        let val = self.line[i];
        let mut j = i;
        let normalized_steps = val.unsigned_abs() % (self.len - 1);
        match val.signum() {
            _ if normalized_steps == 0 => return,
            1 => {
                for _ in 0..normalized_steps {
                    j = next[j];
                    // To understand the following, I needed to cheak
                    if j == i {
                        j = next[j];
                    }
                }
            }
            -1 => {
                for _ in 0..normalized_steps {
                    j = prev[j];
                    if j == i {
                        j = prev[j];
                    }
                }
                j = prev[j];
            }
            _ => unreachable!(),
        }
        // println!(
        //     "{} moves between {} and {}:",
        //     self.line[i], self.line[j], self.line[next[j]]
        // );
        let prev_i = prev[i];
        let next_i = next[i];
        let next_j = next[j];
        debug_assert_ne!(i, j);
        debug_assert_ne!(i, next_i);
        debug_assert_ne!(i, prev_i);
        debug_assert_ne!(i, next_j); // we are supposed to have skipped this situation.
        debug_assert_ne!(j, next_j);
        next[prev_i] = next_i;
        next[j] = i;
        next[i] = next_j;

        prev[next_j] = i;
        prev[i] = j;
        prev[next_i] = prev_i;
    }
    #[allow(dead_code)]
    fn print(&self, next: &[usize]) {
        let mut i = self.index_zero;
        while next[i] != 0 {
            i = next[i];
            print!("{}, ", self.line[i]);
        }
        println!();
    }
    fn value(&self, next: &[usize]) -> isize {
        let mut i = self.index_zero;
        let mut val = 0;
        for count in 1..=3000 {
            i = next[i];
            if [1000, 2000, 3000].contains(&count) {
                val += self.line[i];
            }
        }
        val
    }
    fn is_sound(&self, next: &[usize]) -> bool {
        let mut i = self.index_zero;
        for _ in 0..self.len {
            i = next[i];
        }
        self.line[i] == 0
    }
    #[allow(dead_code)]
    fn trace(&self, next: &[usize]) {
        let mut i = self.index_zero;
        let mut count = 0;
        while self.line[next[i]] != 0 {
            if [2248913542963, -146086047540, 2162885092745].contains(&self.line[i]) {
                println!("{} @ {count}", self.line[i]);
            }
            i = next[i];
            count += 1;
        }
        println!("zero @ {i}");
        assert_eq!(count + 1, self.len);
        println!();
    }
}
