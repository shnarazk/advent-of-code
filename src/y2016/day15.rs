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
        let offset = self.line.len() + 1;
        if let Ok(n) = numbers.captures(block).ok_or(ParseError) {
            let n2 = n[2].parse::<usize>().expect("-");
            let n4 = n[4].parse::<usize>().expect("-");
            let n_4 = (n4 + offset) % n2;
            self.line.push((n2, n_4));
        }
        Ok(())
    }
    fn part1(&mut self) -> usize {
        assert_eq!(chinese((5, 0), (2, 1)).1, 5);
        let mut x = self.line[0];
        for tuple in self.line.iter().skip(1) {
            let offset = if tuple.1 <= tuple.0 {
                tuple.0 - tuple.1
            } else {
                println!("逆転{}, {}", tuple.0, tuple.1);
                (tuple.0 * tuple.1 - tuple.1) % tuple.0
            };
            println!("周期{}で{}余る", tuple.0, offset);
            // x = chinese(x, (tuple.0, offset));
            x = chinese(x, *tuple);
            // assert_eq!(tuple.0 - x.1 % tuple.0, tuple.1);
        }
        x.1
    }
    fn part2(&mut self) -> usize {
        // let mut x = self.bus[0];
        // for tuple in self.bus.iter().skip(1) {
        //     let offset = if tuple.1 <= tuple.0 {
        //         tuple.0 - tuple.1
        //     } else {
        //         println!("逆転{}, {}", tuple.0, tuple.1);
        //         (tuple.0 * tuple.1 - tuple.1) % tuple.0
        //     };
        //     println!("周期{}で{}余る", tuple.0, offset);
        //     x = chinese(x, (tuple.0, offset));
        //     //assert_eq!(tuple.0 - x.1 % tuple.0, tuple.1);
        // }
        // x.1
        0
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
