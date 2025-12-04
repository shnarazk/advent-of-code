//! <https://adventofcode.com/2025/day/2>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    rayon::prelude::*,
    std::collections::HashSet,
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
       桁が下限と上限で違う時は最初に分割すればいいんじゃね。
    */
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|(rs, re)| calc(*rs, *re, 2))
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .par_iter()
            .map(|(rs, re)| calc2(*rs, *re))
            .sum::<usize>()
    }
}

// assert_eq!(window(123456, 1, 0), 1);
// assert_eq!(window(123456, 1, 1), 2);
// assert_eq!(window(123456, 1, 2), 3);
// assert_eq!(window(12345678, 2, 3), 78);
// assert_eq!(window(1234567890, 2, 3), 78);
// assert_eq!(window(1234567890, 2, 4), 90);
fn window(mut n: usize, w: u32, i: u32) -> usize {
    let len = n.ilog10() + 1;
    n /= 10_usize.pow(len - w * (i + 1));
    n % 10_usize.pow(w)
}

fn repeat_window(n: usize, r: u32) -> usize {
    let s = n.ilog10() + 1;
    let found = (1..r).fold(n, |acc, _| acc * 10_usize.pow(s) + n);
    found
}

fn calc(mut s: usize, mut e: usize, r: u32) -> usize {
    let mut s_len = s.ilog10() + 1;
    let mut e_len = e.ilog10() + 1;
    if s_len % r != 0 {
        s_len = (s_len / r + 1) * r;
        s = 10_usize.pow(s_len as u32 - 1);
    }
    if e_len % r != 0 {
        e_len = (e_len / r) * r;
        e = 10_usize.pow(e_len as u32) - 1;
    }
    if s > e {
        return 0;
    }
    debug_assert_eq!(s.ilog10(), e.ilog10());
    let len = (s.ilog10() + 1) / r;
    let mut total = 0;
    let ss = window(s, len, 0);
    let ee = window(e, len, 0);
    for d in ss + 1..ee {
        total += repeat_window(d, r);
    }
    if ss == ee {
        if (1..r).all(|i| ss >= window(s, len, i) && ss <= window(e, len, i)) {
            total += repeat_window(ss, r);
        }
    } else {
        if (1..r).all(|i| ss >= window(s, len, i)) {
            total += repeat_window(ss, r);
        }
        if (1..r).all(|i| ee <= window(e, len, i)) {
            total += repeat_window(ee, r);
        }
    }
    total
}

fn calc_1(s: usize, e: usize, total: &mut HashSet<usize>) {
    let s_len = s.ilog10() + 1;
    let ss = window(s, 1, 0);
    let ee = e / 10_usize.pow(s_len - 1);
    for d in ss..=ee {
        let x = repeat_window(window(d, 1, 0), s_len + d.ilog10());
        if x >= 10 && s <= x && x <= e {
            total.insert(x);
        }
    }
}

fn calc_n(mut s: usize, mut e: usize, l: u32, total: &mut HashSet<usize>) {
    let e_len = e.ilog10() + 1;
    if e_len / l < 2 {
        return;
    }
    if e_len % l != 0 {
        e = 10_usize.pow(((e_len / l) * l) as u32) - 1;
    }
    let mut s_len = s.ilog10() + 1;
    if s_len % l != 0 {
        s_len = (s_len / l + 1) * l;
        s = 10_usize.pow(s_len as u32 - 1);
    }
    for d in window(s, l, 0)..=window(e, l, 0) {
        let x = repeat_window(d, s_len / l);
        if s <= x && x <= e {
            total.insert(x);
        }
    }
}

fn calc2(s: usize, e: usize) -> usize {
    let mut total: HashSet<usize> = HashSet::new();
    calc_1(s, e, &mut total);
    (2..=8)
        .into_iter()
        .for_each(|l| calc_n(s, e, l, &mut total));
    total.iter().sum::<usize>()
}
