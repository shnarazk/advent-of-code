//! <https://adventofcode.com/2016/day/15>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
}

#[aoc(2016, 15)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let numbers = regex!(r"(\d+)\D+(\d+)\D+(\d+)\D+(\d+)");
        if let Ok(n) = numbers.captures(block).ok_or(ParseError) {
            let n2 = n[2].parse::<usize>().expect("-");
            let n4 = n[4].parse::<usize>().expect("-");
            self.line.push((n2, n4));
        }
        Ok(())
    }
    fn part1(&mut self) -> usize {
        // self.line.clear();
        // self.line.push((5, 4));
        // self.line.push((2, 0));
        // self.line.push((7, 2));
        let mut x = self.line[0];
        for (i, tuple) in self.line.iter().enumerate() {
            let mut m = (tuple.0 + tuple.1 + ((i + 1) % tuple.0)) % tuple.0;
            m = tuple.0 - m;
            println!("周期{}で{}start", tuple.0, m);
            if i == 0 {
                x = (tuple.0, m);
            } else {
                x = chinese(x, (tuple.0, m));
            }
        }
        dbg!(&x);
        let mut vec = self.line.iter().map(|(_, o)| *o).collect::<Vec<_>>();
        for t in 0..=(x.1 + self.line.len()) {
            if x.1 < t + self.line.len() {
                println!("{:>4}: {:?}", t, vec);
            }
            for (i, v) in vec.iter_mut().enumerate() {
                *v = (*v + 1) % self.line[i].0;
            }
            if t == x.1 {
                println!("-------------------");
            }
        }
        x.1
    }
    fn part2(&mut self) -> usize {
        self.line.push((11, 0));
        let mut x = self.line[0];
        for (i, tuple) in self.line.iter().enumerate() {
            let mut m = (tuple.0 + tuple.1 + ((i + 1) % tuple.0)) % tuple.0;
            m = tuple.0 - m;
            println!("周期{}で{}start", tuple.0, m);
            if i == 0 {
                x = (tuple.0, m);
            } else {
                x = chinese(x, (tuple.0, m));
            }
        }
        x.1
    }
}

/// Return `x` such that:
/// * x `mod` aq = ar
/// * x `mod` bq = br
///
/// ```
/// use crate::adventofcode::y2016::day15::*;
/// let a = chinese((5, 4), (2, 0));
/// assert_eq!(a.1, 5);
/// ```
pub fn chinese((aq, ar): (usize, usize), (bq, br): (usize, usize)) -> (usize, usize) {
    let n = solve1(aq, bq);
    let nar = (n * ar) % bq;
    let nbr = (n * br) % bq;
    let m = if nar < nbr {
        nbr - nar
    } else {
        (bq + nbr) - nar
    };
    (aq * bq, aq * m + ar)
}

/// Return `X` such that:
/// (X * a) `mod` m = ((X * b) `mod` m) + 1
///
fn solve1(a: usize, m: usize) -> usize {
    for i in 0.. {
        if (i * a) % m == 1 {
            return i;
        }
    }
    panic!("can't");
}

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    #[test]
    fn test_chinese() {
        let a = chinese((3, 2), (5, 3));
        assert_eq!(a.1, 8);
        let c = chinese(a, (2, 7));
        assert_eq!(c.1, 23);
    }

    #[test]
    fn test_part1() {
        assert_eq!(
            Puzzle::solve(Description::FileTag("test".to_string()), 1),
            Answer::Part1(295)
        );
    }
    #[test]
    fn test_part2() {
        assert_eq!(
            Puzzle::solve(Description::FileTag("test".to_string()), 2),
            Answer::Part2(1068781)
        );
    }
}
