//! <https://adventofcode.com/2024/day/14>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::*,
        parser::parse_isize,
        progress_picture,
    },
    rayon::prelude::*,
    rustc_data_structures::fx::{FxHashSet, FxHasher},
    serde::Serialize,
    std::{cmp::Ordering, collections::HashSet, hash::BuildHasherDefault},
    winnow::{
        ascii::newline,
        combinator::{separated, seq},
        PResult, Parser,
    },
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<(isize, isize, isize, isize)>,
    size: (isize, isize),
}

impl Puzzle {
    #[allow(dead_code)]
    fn dump(&self, set: &FxHashSet<(isize, isize)>) {
        let mut s: String = String::new();
        for i in 0..self.size.0 {
            for j in 0..self.size.1 {
                s.push_str(if set.contains(&(i, j)) { "#" } else { "." });
            }
            s.push('\n');
        }
        progress_picture!(s);
    }
}

// p=0,4 v=3,-3
fn parse_line(s: &mut &str) -> PResult<(isize, isize, isize, isize)> {
    seq!(
        _: "p=", parse_isize, _: ",", parse_isize,
        _: " v=", parse_isize, _: ",", parse_isize)
    .map(|(x, y, dx, dy)| (y, x, dy, dx))
    .parse_next(s)
}
fn parse(s: &mut &str) -> PResult<Vec<(isize, isize, isize, isize)>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc(2024, 14)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let s = &mut input.as_str();
        self.line = parse(s)?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        self.size = match &self.get_config().alt {
            Some(x) if x.as_str() == "0" => (7, 11),
            _ => (103, 101),
        };
    }
    fn part1(&mut self) -> Self::Output1 {
        let t = 100;
        let hy = self.size.0 / 2;
        let hx = self.size.1 / 2;
        let res = self
            .line
            .iter()
            .map(|&(pi, pj, si, sj)| {
                let a = (((t * si + pi) % self.size.0) + self.size.0) % self.size.0;
                let b = (((t * sj + pj) % self.size.1) + self.size.1) % self.size.1;
                // println!("{a:>2}, {b:>2}");
                match ((a).cmp(&hy), (b).cmp(&hx)) {
                    (Ordering::Equal, _) | (_, Ordering::Equal) => (0, 0, 0, 0),
                    (Ordering::Less, Ordering::Less) => (1, 0, 0, 0),
                    (Ordering::Less, Ordering::Greater) => (0, 1, 0, 0),
                    (Ordering::Greater, Ordering::Less) => (0, 0, 1, 0),
                    (Ordering::Greater, Ordering::Greater) => (0, 0, 0, 1),
                }
            })
            .fold((0, 0, 0, 0), |acc, val| {
                (acc.0 + val.0, acc.1 + val.1, acc.2 + val.2, acc.3 + val.3)
            });
        res.0 * res.1 * res.2 * res.3
    }
    fn part2(&mut self) -> Self::Output2 {
        let decay_rate: f64 = 0.9;
        let num_points = self.line.len();
        let mut signal_rate_ema = 1.0;
        for t in 1.. {
            let res = self
                .line
                .par_iter()
                .map(|&(pi, pj, si, sj)| {
                    (
                        (((t * si + pi) % self.size.0) + self.size.0) % self.size.0,
                        (((t * sj + pj) % self.size.1) + self.size.1) % self.size.1,
                    )
                })
                .collect::<HashSet<_, BuildHasherDefault<FxHasher>>>();
            let num_connected = res
                .par_iter()
                .filter(|p| {
                    p.neighbors4((0, 0), self.size)
                        .iter()
                        .any(|q| res.contains(q))
                })
                .count();
            let r = num_connected as f64 / num_points as f64;
            if 4.0 < r / signal_rate_ema {
                return t as usize;
            }
            signal_rate_ema *= decay_rate;
            signal_rate_ema += (1.0 - decay_rate) * r;
        }
        unreachable!()
    }
    fn serialize(&self) -> Option<String> {
        let mut hist_ema: Vec<f64> = Vec::new();
        let mut hist_value: Vec<f64> = Vec::new();
        let mut hist_trend: Vec<f64> = Vec::new();
        let mut goal: Option<isize> = None;

        let decay_rate: f64 = 0.95;
        let num_points = self.line.len();
        let mut signal_rate_ema = 0.15;
        for t in 1.. {
            let res = self
                .line
                .par_iter()
                .map(|&(pi, pj, si, sj)| {
                    (
                        (((t * si + pi) % self.size.0) + self.size.0) % self.size.0,
                        (((t * sj + pj) % self.size.1) + self.size.1) % self.size.1,
                    )
                })
                .collect::<HashSet<_, BuildHasherDefault<FxHasher>>>();
            let num_connected = res
                .par_iter()
                .filter(|p| {
                    p.neighbors4((0, 0), self.size)
                        .iter()
                        .any(|q| res.contains(q))
                })
                .count();
            let r = num_connected as f64 / num_points as f64;
            if 4.0 < r / signal_rate_ema && goal.is_none() {
                goal = Some(t + 100);
            }
            hist_value.push(r);
            hist_trend.push(r / signal_rate_ema);
            signal_rate_ema *= decay_rate;
            signal_rate_ema += (1.0 - decay_rate) * r;
            hist_ema.push(signal_rate_ema);
            if goal.is_some_and(|limit| limit < t) {
                break;
            }
        }
        #[derive(Serialize)]
        struct Record {
            ema: Vec<f64>,
            value: Vec<f64>,
            trend: Vec<f64>,
        }
        let record = Record {
            ema: hist_ema,
            value: hist_value,
            trend: hist_trend,
        };
        serde_json::to_string(&record).map_or_else(|_| None, |v| Some(v))
    }
}
