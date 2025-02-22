//! <https://adventofcode.com/2023/day/5>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    itertools::Itertools,
};

// A half-open range implementation
type Range = (usize, usize);

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    seeds: Vec<usize>,
    line: Vec<Vec<(usize, usize, usize)>>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline, space1},
            combinator::{separated, seq},
        },
    };

    fn parse_seeds(s: &mut &str) -> ModalResult<Vec<usize>> {
        seq!(_: "seeds: ",  separated(1.., parse_usize, space1))
            .map(|(v,)| v)
            .parse_next(s)
    }

    fn parse_block(s: &mut &str) -> ModalResult<Vec<(usize, usize, usize)>> {
        seq!(
            _: (alpha1, "-to-", alpha1, " map:\n"),
            separated(1.., separated(3, parse_usize, " ").map(|v: Vec<usize>| (v[0], v[1], v[1] + v[2])), newline)
                .map(|v: Vec<(usize, usize, usize)>| v)
        )
        .map(|(v,)| v)
        .parse_next(s)
    }

    #[allow(clippy::type_complexity)]
    pub fn parse(s: &mut &str) -> ModalResult<(Vec<usize>, Vec<Vec<(usize, usize, usize)>>)> {
        seq!(parse_seeds, _: (newline, newline), separated(1.., parse_block, (newline, newline)))
            .parse_next(s)
    }
}

#[aoc(2023, 5)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        let (seeds, rules) = parser::parse(&mut input)?;
        self.seeds = seeds;
        self.line = rules;
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
