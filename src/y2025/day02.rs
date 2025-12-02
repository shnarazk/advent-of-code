//! <https://adventofcode.com/2025/day/2>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    rayon::prelude::*,
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            combinator::{separated, seq},
        },
    };
    fn parse_line(s: &mut &str) -> ModalResult<(usize, usize)> {
        seq!(parse_usize, "-", parse_usize)
            .parse_next(s)
            .map(|(a, _, b)| (a, b))
    }
    pub fn parse(s: &mut &str) -> ModalResult<Vec<(usize, usize)>> {
        separated(1.., parse_line, ",").parse_next(s)
    }
}

#[aoc(2025, 2)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    /*
       2514-3613の考え方：
       26から始まるパターンから35から始まるパターンまでは無条件に題意を満たすのでこの時点で10個見つかる。
       25から始まるパターンすなわち2525は下位2桁が14よりも大きいので対象。
       36から始まるパターンすなわち3636は下位2桁が13よりも大きいので対象外。
       ということで下位セグメント（群）が作る制約を全て満たすものを列挙すればよい。
    */
    fn part1(&mut self) -> Self::Output1 {
        assert_eq!(window(123456, 1, 0), 1);
        assert_eq!(window(123456, 1, 1), 2);
        assert_eq!(window(123456, 1, 2), 3);
        assert_eq!(window(12345678, 2, 3), 78);
        assert_eq!(window(1234567890, 2, 3), 78);
        assert_eq!(window(1234567890, 2, 4), 90);
        self.line
            .iter()
            .map(|(s, e)| {
                (*s..*e)
                    .into_par_iter()
                    .map(|n| {
                        check_occurences(n)
                            .and_then(|_| satisfies(n).then(|| n))
                            .unwrap_or(0)
                    })
                    .sum::<usize>()
            })
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .map(|(s, e)| {
                (*s..*e)
                    .into_par_iter()
                    .map(|n| {
                        check_occurences(n)
                            .and_then(|k| satisfies2(n, k).then(|| n))
                            .unwrap_or(0)
                    })
                    .sum::<usize>()
            })
            .sum::<usize>()
    }
}

// assert_eq!(window(123456, 1, 0), 1);
// assert_eq!(window(123456, 1, 1), 2);
// assert_eq!(window(123456, 1, 2), 3);
// assert_eq!(window(12345678, 2, 3), 78);
// assert_eq!(window(1234567890, 2, 3), 78);
// assert_eq!(window(1234567890, 2, 4), 90);
fn window(mut n: usize, w: usize, i: usize) -> usize {
    let len = n.ilog10() + 1;
    // dbg!(len);
    n /= 10_usize.pow(len - (w * (i + 1)) as u32);
    // dbg!(n);
    n % 10_usize.pow(w as u32)
}

fn check_occurences(mut n: usize) -> Option<u8> {
    let mut occs = [0_u8; 10];
    while n > 0 {
        occs[n % 10] += 1;
        n /= 10;
    }
    let k = *occs.iter().filter(|k| **k > 0).min().unwrap();
    (k > 1 && occs.iter().all(|o| *o % k == 0)).then_some(k)
}

fn satisfies(n: usize) -> bool {
    let v = vectorize(n);
    let offset = v.len() / 2;
    v[..offset] == v[offset..]
}

fn satisfies2(n: usize, k: u8) -> bool {
    let v = vectorize(n);
    for m in [2, 3, 5, 7, 11, 13, 17] {
        if k % m == 0 {
            let l = v.len() / m as usize;
            if (1..m as usize).all(|r| v[..l] == v[r * l..(r + 1) * l]) {
                return true;
            }
        }
    }
    false
}

fn vectorize(mut n: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::new();
    while n > 0 {
        v.push((n % 10) as u8);
        n /= 10;
    }
    v.reverse();
    v
}
