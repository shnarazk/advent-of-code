//! <https://adventofcode.com/2023/day/12>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser,
    },
    std::{cmp::Ordering, collections::HashMap},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(Vec<usize>, Vec<usize>)>,
}

#[aoc(2023, 12)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let mut tuple = (Vec::new(), Vec::new());
        for (i, segment) in block.split(' ').enumerate() {
            if i == 1 {
                let nums = parser::to_usizes(segment, &[',']).unwrap();
                tuple.1 = nums;
            } else {
                let vals = segment
                    .chars()
                    .map(|c| match c {
                        '.' => 0,
                        '#' => 1,
                        '?' => 2,
                        _ => unreachable!(),
                    })
                    .collect::<Vec<usize>>();
                tuple.0 = vals;
            }
        }
        self.line.push(tuple);
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .map(|(k, s)| {
                let mut hash: HashMap<(Vec<usize>, usize), usize> = HashMap::new();
                match_sequences(&mut hash, k, s)
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .map(|(k, s)| {
                let mut hash: HashMap<(Vec<usize>, usize), usize> = HashMap::new();
                let k5 = (0..5).map(|_| k.clone()).collect::<Vec<_>>().join(&2);
                let s5 = s
                    .iter()
                    .cycle()
                    .take(s.len() * 5)
                    .copied()
                    .collect::<Vec<_>>();
                match_sequences(&mut hash, &k5, &s5)
            })
            .sum()
    }
}

fn match_sequences(
    hash: &mut HashMap<(Vec<usize>, usize), usize>,
    a: &[usize],
    b: &[usize],
) -> usize {
    let k = (a.to_vec(), b.len());
    if let Some(c) = hash.get(&k) {
        return *c;
    }
    let x = match_sequences_aux(hash, a, b);
    hash.insert(k, x);
    x
}

fn match_sequences_aux(
    hash: &mut HashMap<(Vec<usize>, usize), usize>,
    a: &[usize],
    b: &[usize],
) -> usize {
    match (a.is_empty(), b.is_empty()) {
        (true, true) => return 1,
        (false, true) => return a.iter().all(|c| *c != 1) as usize,
        (true, false) => return 0,
        _ => (),
    }
    if a.len() < b.iter().sum() {
        return 0;
    }
    let beg = a[0];
    let ends_at = a
        .iter()
        .enumerate()
        .find(|(_, c)| **c != beg)
        .map_or(a.len(), |(i, _)| i);
    match beg {
        0 => match_sequences(hash, &a[1..], b),
        1 => match b[0].cmp(&ends_at) {
            Ordering::Less => 0,
            Ordering::Equal if b[0] == a.len() => {
                assert!(b.len() == 1); // wrong assumption??
                1 // ?? (b.len() == 1) as usize
            }
            Ordering::Equal => match a[b[0]] {
                0 | 2 => match_sequences(hash, &a[b[0] + 1..], &b[1..]),
                _ => unreachable!(),
            },
            Ordering::Greater => {
                if (ends_at..b[0]).all(|i| a[i] != 0) && (b[0] == a.len() || a[b[0]] != 1) {
                    if a.len() < b[0] + 1 {
                        (b.len() == 1) as usize
                    } else {
                        match_sequences(hash, &a[b[0] + 1..], &b[1..])
                    }
                } else {
                    0
                }
            }
        },
        2 => {
            let mut v = a.to_vec();
            v[0] = 0;
            let c0 = match_sequences(hash, &v, b);
            v[0] = 1;
            let c1 = match_sequences(hash, &v, b);
            c0 + c1
        }
        _ => unreachable!(),
    }
}
