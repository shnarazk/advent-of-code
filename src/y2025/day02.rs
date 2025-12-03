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
       桁が下限と上限で違う時は最初に分割すればいいんじゃね。
    */
    fn part1(&mut self) -> Self::Output1 {
        assert_eq!(window(123456, 1, 0), 1);
        assert_eq!(window(123456, 1, 1), 2);
        assert_eq!(window(123456, 1, 2), 3);
        assert_eq!(window(12345678, 2, 3), 78);
        assert_eq!(window(1234567890, 2, 3), 78);
        assert_eq!(window(1234567890, 2, 4), 90);
        // dbg!(window(123456789, 5, 0));
        self.line
            .iter()
            .map(|(rs, re)| {
                let mut s = *rs;
                let mut e = *re;
                // dbg!(s, e);
                let s_len = s.ilog10() + 1;
                let e_len = e.ilog10() + 1;
                if s_len % 2 == 1 {
                    s = 10_usize.pow(s_len as u32);
                }
                if e_len % 2 == 1 {
                    e = 10_usize.pow(e_len as u32 - 1) - 1;
                }
                if s > e {
                    return 0;
                }
                assert_eq!(s.ilog10(), e.ilog10());
                let len2 = (s.ilog10() + 1) / 2;
                // dbg!(window(s, len / 2, 0), window(e, len / 2, 0));
                let mut total = 0;
                let ss = window(s, len2, 0);
                let ee = window(e, len2, 0);
                for d in ss + 1..ee {
                    total += d * 10_usize.pow(len2) + d;
                }
                if ss == ee {
                    if ss >= window(s, len2, 1) && ss <= window(e, len2, 1) {
                        total += ss * 10_usize.pow(len2) + ss;
                    }
                } else {
                    if ss >= window(s, len2, 1) {
                        total += ss * 10_usize.pow(len2) + ss;
                    }
                    if ee <= window(e, len2, 1) {
                        total += ee * 10_usize.pow(len2) + ee;
                    }
                }
                total
            })
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        0
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
    // dbg!(len);
    n /= 10_usize.pow(len - w * (i + 1));
    // dbg!(n);
    n % 10_usize.pow(w)
}
