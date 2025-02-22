//! <https://adventofcode.com/2020/day/13>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    time: usize,
    bus: Vec<(usize, usize)>,
}

#[aoc(2020, 13)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        for block in input.split("\n\n").filter(|l| !l.is_empty()) {
            let mut iter = block.split('\n');
            self.time = iter.next().unwrap().parse::<usize>().unwrap();
            for (i, b) in iter.next().unwrap().split(',').enumerate() {
                if let Ok(n) = b.parse::<usize>() {
                    self.bus.push((n, i));
                }
            }
        }
        Ok(())
    }
    fn part1(&mut self) -> usize {
        let mut bus: usize = self.bus[0].0;
        let mut wait = usize::MAX;
        for (cycle, _) in self.bus.iter() {
            let before = self.time % cycle;
            if before == 0 {
                return 0;
            }
            let w = cycle - before;
            if w < wait {
                wait = w;
                bus = *cycle;
            }
        }
        wait * bus
    }
    fn part2(&mut self) -> usize {
        let verbose = !self.get_config().bench;
        let mut x = self.bus[0];
        for tuple in self.bus.iter().skip(1) {
            let offset = if tuple.1 <= tuple.0 {
                tuple.0 - tuple.1
            } else {
                if verbose {
                    println!("逆転{}, {}", tuple.0, tuple.1);
                }
                (tuple.0 * tuple.1 - tuple.1) % tuple.0
            };
            if verbose {
                println!("周期{}で{}余る", tuple.0, offset);
            }
            x = chinese(x, (tuple.0, offset));
            //assert_eq!(tuple.0 - x.1 % tuple.0, tuple.1);
        }
        x.1
    }
}

/// Return `x` such that:
/// * x `mod` aq = am
/// * x `mod` bq = bm
///
/// ```
/// use crate::adventofcode::y2020::day13::*;
/// let a = chinese((3, 2), (5, 3));
/// assert_eq!(a.1, 8);
/// let b = chinese(a, (2, 7));
/// assert_eq!(b.1, 23);
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
