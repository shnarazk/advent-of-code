//! <https://adventofcode.com/2024/day/11>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser,
    },
    serde::Serialize,
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Puzzle {
    line: Vec<usize>,
}

fn even_digits(n: usize) -> Option<(usize, usize)> {
    fn aux(n: usize, digits: usize, origin: usize) -> Option<(usize, usize)> {
        if n < 10 {
            if digits % 2 == 0 {
                let half = 10_usize.pow(digits as u32 / 2);
                Some((origin / half, origin % half))
            } else {
                None
            }
        } else {
            aux(n / 10, digits + 1, origin)
        }
    }
    aux(n, 1, n)
}

fn num_edges(threshold: usize, depth: usize, val: usize) -> usize {
    if depth == threshold {
        1
    } else if val == 0 {
        num_edges(threshold, depth + 1, 1)
    } else if let Some((l, r)) = even_digits(val) {
        num_edges(threshold, depth + 1, l) + num_edges(threshold, depth + 1, r)
    } else {
        num_edges(threshold, depth + 1, val * 2024)
    }
}

fn num_edges2(
    threshold: usize,
    depth: usize,
    vals: HashMap<usize, usize>,
) -> HashMap<usize, usize> {
    if depth == threshold {
        return vals;
    }
    let mut ret: HashMap<usize, usize> = HashMap::new();
    for (&val, &count) in vals.iter() {
        if val == 0 {
            *ret.entry(1).or_default() += count;
        } else if let Some((l, r)) = even_digits(val) {
            *ret.entry(l).or_default() += count;
            *ret.entry(r).or_default() += count;
        } else {
            *ret.entry(val * 2024).or_default() += count;
        }
    }
    num_edges2(threshold, depth + 1, ret)
}

#[aoc(2024, 11)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parser::to_usizes(input.as_str(), &[' ']).expect("ng");
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().map(|&n| num_edges(25, 0, n)).sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let vals: HashMap<usize, usize> = self
            .line
            .iter()
            .map(|&n| (n, 1))
            .collect::<HashMap<usize, usize>>();
        num_edges2(75, 0, vals).values().sum()
    }
}
