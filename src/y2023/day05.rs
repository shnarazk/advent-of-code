//! <https://adventofcode.com/2023/day/5>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    itertools::Itertools,
    winnow::{
        ascii::{dec_uint, newline, not_line_ending, space1},
        multi::separated1,
        sequence::preceded,
        IResult, Parser,
    },
};

// A half-open range implementation
type Range = (usize, usize);

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    seeds: Vec<usize>,
    line: Vec<Vec<(usize, usize, usize)>>,
}

fn u64<I, E: winnow::error::ParseError<I>>(input: I) -> IResult<I, u64, E>
where
    I: winnow::stream::StreamIsPartial + winnow::stream::Stream,
    <I as winnow::stream::Stream>::Token: winnow::stream::AsChar + Copy,
{
    dec_uint(input)
}

fn parse_line<I, E: winnow::error::ParseError<I>>(str: I) -> IResult<I, Vec<u64>, E>
where
    I: winnow::stream::StreamIsPartial + winnow::stream::Stream,
    <I as winnow::stream::Stream>::Token: winnow::stream::AsChar + Copy,
{
    separated1(u64, space1).parse_next(str)
}

fn parse_line_usize(str: &str) -> IResult<&str, Vec<usize>> {
    let (remain1, v): (&str, Vec<u64>) = parse_line(str)?;
    Ok((remain1, v.iter().map(|l| *l as usize).collect::<Vec<_>>()))
}

/* fn parse_block(str: &str) -> IResult<&str, Vec<(usize, usize, usize)>> {
    let (remain1, _) = preceded(not_line_ending, newline)(str)?;
    let (remain2, v): (&str, Vec<Vec<u64>>) = separated1(parse_line, newline)(remain1)?;
    Ok((
        remain2,
        v.iter()
            .map(|l| (l[0] as usize, l[1] as usize, (l[1] + l[2]) as usize))
            .collect::<Vec<_>>(),
    ))
} */

#[aoc(2023, 5)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        fn parse_block(str: &str) -> IResult<&str, Vec<(usize, usize, usize)>> {
            let (remain1, _) = preceded(not_line_ending, newline).parse_next(str)?;
            let (remain2, v): (&str, Vec<Vec<u64>>) =
                separated1(parse_line, newline).parse_next(remain1)?;
            Ok((
                remain2,
                v.iter()
                    .map(|l| (l[0] as usize, l[1] as usize, (l[1] + l[2]) as usize))
                    .collect::<Vec<_>>(),
            ))
        }
        if block.starts_with("seeds:") {
            let vals = block.split(": ").nth(1).unwrap().trim();
            self.seeds = parse_line_usize(vals).expect("error").1;
            return Ok(());
        }
        let (_, v) = parse_block(block)?;
        self.line.push(v);
        Ok(())
    }
    #[allow(clippy::unnecessary_lazy_evaluations)]
    fn part1(&mut self) -> Self::Output1 {
        let mut locs = self.seeds.clone();
        for trans in self.line.iter() {
            for p in locs.iter_mut() {
                for (d, s, t) in trans.iter() {
                    let map = |pos: usize| (*s <= pos && pos < *t).then(|| *d + pos - *s);
                    if let Some(d) = map(*p) {
                        *p = d;
                        break;
                    }
                }
            }
        }
        *locs.iter().min().unwrap()
    }
    #[allow(clippy::unnecessary_lazy_evaluations)]
    fn part2(&mut self) -> Self::Output2 {
        let mut ranges: Vec<Range> = self
            .seeds
            .iter()
            .tuples()
            .map(|(a, b)| (*a, *a + *b)) // store as half-close range
            .collect::<Vec<Range>>();
        for trans in self.line.iter() {
            let mut handled: Vec<Range> = Vec::new();
            for (d, s, t) in trans.iter() {
                let mapb = |pos: usize| (*s <= pos && pos < *t).then(|| *d + pos - *s);
                let mape = |pos: usize| (*s <= pos && pos <= *t).then(|| *d + pos - *s);
                let map = |b, e| (mapb(b).unwrap(), mape(e).unwrap());
                let mut unhandled: Vec<Range> = Vec::new();
                for r in ranges.iter() {
                    if (r.0 < *s) && (r.1 < *s) {
                        unhandled.push(*r);
                        continue;
                    }
                    if (r.0 < *s) && (r.1 <= *t) {
                        // divide two segments
                        let div: usize = *s;
                        let r1: Range = (r.0, div);
                        let r2: Range = map(div, r.1);
                        unhandled.push(r1);
                        handled.push(r2);
                        continue;
                    }
                    if (r.0 < *s) && (*t < r.1) {
                        // divide three segments
                        let div1: usize = *s;
                        let div2: usize = *t;
                        let r1: Range = (r.0, div1);
                        let r2: Range = map(div1, div2);
                        let r3: Range = (div2, r.1);
                        unhandled.push(r1);
                        handled.push(r2);
                        unhandled.push(r3);
                        continue;
                    }
                    if (r.0 <= *t) && (r.1 <= *t) {
                        // shifted the entire range
                        let r0 = map(r.0, r.1);
                        handled.push(r0);
                        continue;
                    }
                    if (r.0 <= *t) && (*t < r.1) {
                        // divide two segments
                        let div: usize = *t;
                        let r1: Range = map(r.0, div);
                        let r2: Range = (div, r.1);
                        handled.push(r1);
                        unhandled.push(r2);
                        continue;
                    }
                    unhandled.push(*r);
                }
                ranges = unhandled;
            }
            ranges.append(&mut handled);
        }
        ranges.iter().map(|(b, _)| *b).min().unwrap()
    }
}
