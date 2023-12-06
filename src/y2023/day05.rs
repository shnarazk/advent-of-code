//! <https://adventofcode.com/2023/day/5>

use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        line_parser,
    },
    itertools::Itertools,
};

// A half-open range implementation
type Range = (usize, usize);

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    seeds: Vec<usize>,
    line: Vec<Vec<(usize, usize, usize)>>,
}

#[aoc(2023, 5)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let mut v = Vec::new();
        for (i, line) in block.trim().split('\n').enumerate() {
            if line.starts_with("seeds:") {
                let vals = line.split(": ").nth(1).unwrap().trim();
                self.seeds = line_parser::to_usizes(vals, ' ')?;
                continue;
            }
            if i == 0 {
                continue;
            }
            let t = line_parser::to_usizes(line, ' ')?;
            v.push((t[0], t[1], t[1] + t[2]));
        }
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
