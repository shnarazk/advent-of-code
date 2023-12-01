//! <https://adventofcode.com/2019/day/22>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
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
        if stack.captures(block).is_some() {
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
    fn end_of_data(&mut self) {
        // dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .fold(2019_usize, |i, s| s.part1().shuffle(i))
    }
    /// to the world of Linear Congruential Functions
    /// https://codeforces.com/blog/entry/72593
    /// https://www.reddit.com/r/adventofcode/comments/engeuy/comment/fdzr3d5/?utm_source=reddit&utm_medium=web2x&context=3
    fn part2(&mut self) -> Self::Output2 {
        const N: usize = PART2_SIZE;
        const K: usize = 101741582076661;
        // check the correctness of inverting functions
        for i in 1..1000 {
            assert!(Shuffle::<N>::Stack.cancel(Shuffle::<N>::Stack.shuffle(i)) == i);
            assert!(
                Shuffle::<N>::Cut(i as isize).cancel(Shuffle::<N>::Cut(i as isize).shuffle(i)) == i
            );
            assert!(Shuffle::<N>::Increment(i).cancel(Shuffle::<N>::Increment(i).shuffle(i)) == i);
        }
        let start: usize = 2020;
        // Build the converting LCF
        let suit = self.line.iter().rev().map(|t| t.part2());
        let b = suit.clone().fold(0, |i, t| t.cancel(i));
        let a = {
            let a_b = suit.clone().fold(1, |i, t| t.cancel(i));
            (a_b + 2 * N - b) % N
        };
        {
            // test the correctness of the coefficients
            let step2 = suit.clone().fold(b, |i, t| t.cancel(i));
            assert_eq!(
                step2,
                ((b as u128 + (b as u128) * (a as u128)) % (N as u128)) as usize
            );
        }
        let convert = Lcf::<N>(a, b).pow(K);
        let result = convert.eval(start);
        {
            // test the unitness
            let suit = self.line.iter().map(|t| t.part2());
            let b = suit.clone().fold(0, |i, t| t.shuffle(i));
            let a = {
                let a_b = suit.clone().fold(1, |i, t| t.shuffle(i));
                (a_b + 2 * N - b) % N
            };
            assert_eq!(Lcf::<N>(a, b).pow(K).eval(result), start);
        }
        result
    }
}

/// Linear Congruential Function
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct Lcf<const N: usize>(usize, usize);

impl<const N: usize> Default for Lcf<N> {
    fn default() -> Self {
        Lcf(1, 0)
    }
}
impl<const N: usize> Lcf<N> {
    fn eval(&self, n: usize) -> usize {
        ((self.0 as u128 * n as u128 + self.1 as u128) % N as u128) as usize
    }
    fn compose(&self, other: Lcf<N>) -> Lcf<N> {
        Lcf::<N>(
            ((self.0 as u128 * other.0 as u128) % N as u128) as usize,
            ((self.1 as u128 * other.0 as u128 + other.1 as u128) % N as u128) as usize,
        )
    }
    fn pow(&self, p: usize) -> Lcf<N> {
        let mut f = *self;
        let mut g = Lcf::default();
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
