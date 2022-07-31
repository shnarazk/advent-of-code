//! <https://adventofcode.com/2019/day/22>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashSet,
};

#[derive(Debug, Eq, Hash, PartialEq)]
enum Shuffle<const N: usize> {
    Stack,
    Cut(isize),
    Increment(usize),
}
const PART1_SIZE: usize = 10007;
const PART2_SIZE: usize = 119315717514047;

impl<const N: usize> Shuffle<N> {
    fn part1(&self) -> Shuffle<PART1_SIZE> {
        match self {
            Self::Stack => Shuffle::<PART1_SIZE>::Stack,
            Self::Cut(c) => Shuffle::<PART1_SIZE>::Cut(*c),
            Self::Increment(i) => Shuffle::<PART1_SIZE>::Increment(*i),
        }
    }
    fn part2(&self) -> Shuffle<PART2_SIZE> {
        match self {
            Self::Stack => Shuffle::<PART2_SIZE>::Stack,
            Self::Cut(c) => Shuffle::<PART2_SIZE>::Cut(*c),
            Self::Increment(i) => Shuffle::<PART2_SIZE>::Increment(*i),
        }
    }
    fn shuffle(&self, n: usize) -> usize {
        match self {
            Shuffle::Stack => N - 1 - n,
            Shuffle::Cut(c) => (((N + n) as isize - *c) as usize) % N,
            Shuffle::Increment(i) => (n * i) % N,
        }
    }
    fn cancel(&self, n: usize) -> usize {
        match self {
            Shuffle::Stack => N - 1 - n,
            Shuffle::Cut(c) => ((n + N) as isize + *c) as usize % N,
            Shuffle::Increment(i) => {
                for x in (0..).map(|k| n + k * N) {
                    if x % i == 0 {
                        return x / i;
                    }
                }
                unreachable!()
            }
        }
    }
}

#[derive(Debug, Default, Eq, Hash, PartialEq)]
pub struct Puzzle {
    line: Vec<Shuffle<0>>,
}

#[aoc(2019, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let stack = regex!(r"^deal into new stack$");
        let cut = regex!(r"^cut (-?\d+)$");
        let increment = regex!(r"^deal with increment (\d+)$");
        if let Some(segment) = stack.captures(block) {
            self.line.push(Shuffle::Stack);
        } else if let Some(segment) = cut.captures(block) {
            let val: isize = segment[1].parse::<isize>()?;
            self.line.push(Shuffle::Cut(val));
        } else if let Some(segment) = increment.captures(block) {
            let val: usize = segment[1].parse::<usize>()?;
            self.line.push(Shuffle::Increment(val));
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .fold(2019_usize, |i, s| s.part1().shuffle(i))
    }
    /// https://www.reddit.com/r/adventofcode/comments/engeuy/comment/fdzr3d5/?utm_source=reddit&utm_medium=web2x&context=3
    fn part2(&mut self) -> Self::Output2 {
        // work in the world of Linear Congruential Functions
        const N: usize = PART2_SIZE;
        const K: usize = 101741582076661;
        let start: usize = 2020;
        let suit = self.line.iter().map(|t| t.part2()).collect::<Vec<_>>();
        let b = suit.iter().fold(0, |i, t| t.cancel(i));
        let m = {
            let b_m = dbg!(suit.iter().fold(1, |i, t| t.cancel(i)));
            (b_m + 2 * N - b) % N
        };
        {
            let step2 = dbg!(suit.iter().fold(b, |i, t| t.cancel(i)));
            assert_eq!(
                step2,
                ((b as u128 + (b as u128) * (m as u128)) % (N as u128)) as usize
            );
        }
        let convert = Lcf::<N>(b, m).pow(K);
        convert.eval(start)
    }
}

/// Linear Congruential Function
#[derive(Copy, Clone, Eq, PartialEq)]
struct Lcf<const N: usize>(usize, usize);

impl<const N: usize> Lcf<N> {
    fn eval(&self, n: usize) -> usize {
        ((self.0 as u128 + self.1 as u128 * n as u128) % N as u128) as usize
    }
    fn compose(&self, other: Lcf<N>) -> Lcf<N> {
        Lcf::<N>(
            ((self.0 as u128 * other.0 as u128) % N as u128) as usize,
            ((self.1 as u128 * other.0 as u128) + other.1 as u128) as usize,
        )
    }
    fn pow(&self, p: usize) -> Lcf<N> {
        let mut f = *self;
        let mut g = Lcf(0, 1);
        let mut k = p;
        while 0 < k {
            if k % 2 == 1 {
                g = g.compose(f);
            }
            k /= 2;
            f = f.compose(f);
        }
        g
    }
}
