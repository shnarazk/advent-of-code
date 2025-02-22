//! <https://adventofcode.com/2023/day/7>

use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    itertools::Itertools,
    std::{cmp::Ordering, collections::HashMap},
};

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
struct Hand {
    card: Vec<u8>,
    bid: usize,
}
impl Hand {
    fn kind(&self) -> usize {
        let mut set: HashMap<u8, u8> = HashMap::new();
        let mut numj = 0;
        for c in self.card.iter() {
            if *c == 0 {
                numj += 1;
                continue;
            }
            *set.entry(*c).or_insert(0) += 1;
        }
        if numj == 5 {
            return 7;
        }
        let m = *set.values().max().unwrap() + numj;
        match set.len() {
            1 => 7,
            2 if m == 4 => 6,
            2 if m == 3 => 5,
            3 if m == 3 => 4,
            3 if m == 2 => 3,
            4 => 2,
            5 => 1,
            _ => unreachable!(),
        }
    }
}

impl Ord for Hand {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.kind().cmp(&other.kind()) {
            Ordering::Equal => self.card.cmp(&other.card),
            otherwise => otherwise,
        }
    }
}

impl PartialOrd for Hand {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line1: Vec<Hand>,
    line2: Vec<Hand>,
}

#[aoc(2023, 7)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            let mut iter = l.split(' ');
            let cs = iter.next().unwrap().chars();
            let bid = iter.next().unwrap().parse::<usize>().unwrap();
            let card1 = cs
                .clone()
                .map(|c| match c {
                    'T' => 10,
                    'J' => 11,
                    'Q' => 12,
                    'K' => 13,
                    'A' => 14,
                    _ => c as u8 - b'0',
                })
                .collect::<Vec<u8>>();
            let card2 = cs
                .map(|c| match c {
                    'J' => 0,
                    'T' => 10,
                    'Q' => 12,
                    'K' => 13,
                    'A' => 14,
                    _ => c as u8 - b'0',
                })
                .collect::<Vec<u8>>();
            self.line1.push(Hand { card: card1, bid });
            self.line2.push(Hand { card: card2, bid });
        }
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        evaluate(&self.line1)
    }
    fn part2(&mut self) -> Self::Output2 {
        evaluate(&self.line2)
    }
}

fn evaluate(v: &[Hand]) -> usize {
    v.iter()
        .sorted()
        .enumerate()
        .map(|(i, p)| (i + 1) * p.bid)
        .sum()
}
