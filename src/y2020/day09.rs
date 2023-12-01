//! <https://adventofcode.com/2020/day/9>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashSet,
};

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    vec: Vec<usize>,
    len: usize,
}

#[aoc(2020, 9)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.vec.push(block.parse::<usize>()?);
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.len = if 100 < self.vec.len() { 25 } else { 5 };
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

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        assert_eq!(
            Puzzle::solve(Description::FileTag("test1".to_string()), 1),
            Answer::Part1(127)
        );
    }
    #[test]
    fn test_part2() {
        assert_eq!(
            Puzzle::solve(Description::FileTag("test1".to_string()), 2),
            Answer::Part2(62)
        );
    }
}
