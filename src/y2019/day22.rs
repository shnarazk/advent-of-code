//! <https://adventofcode.com/2019/day/22>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
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

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Puzzle {
    line: Vec<Shuffle<0>>,
}

mod parser {
    use {
        super::*,
        crate::parser::{parse_isize, parse_usize},
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, separated, seq},
        },
    };

    fn parse_shuffle(s: &mut &str) -> ModalResult<Shuffle<0>> {
        alt((
            "deal into new stack".map(|_| Shuffle::Stack),
            seq!(_: "cut ", parse_isize).map(|(n,): (isize,)| Shuffle::Cut(n)),
            seq!(_: "deal with increment ", parse_usize)
                .map(|(n,): (usize,)| Shuffle::Increment(n)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Shuffle<0>>> {
        separated(1.., parse_shuffle, newline).parse_next(s)
    }
}

#[aoc(2019, 22)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
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
