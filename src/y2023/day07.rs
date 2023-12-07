//! <https://adventofcode.com/2023/day/7>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::{cmp::Ordering, collections::HashMap},
};

#[derive(Debug, Default, Eq, Hash, PartialEq)]
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
        match set.len() {
            0 if numj == 5 => 7,
            1 => 7,
            2 if *set.values().max().unwrap() + numj == 4 => 6,
            2 if *set.values().max().unwrap() + numj == 3 => 5,
            3 if *set.values().max().unwrap() + numj == 3 => 4,
            3 if *set.values().max().unwrap() + numj == 2 => 3,
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
        Some(self.cmp(&other))
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line1: Vec<Hand>,
    line2: Vec<Hand>,
}

#[aoc(2023, 7)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let mut iter = block.split(' ');
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
                _ => c as u8 - '0' as u8,
            })
            .collect::<Vec<u8>>();
        let card2 = cs
            .map(|c| match c {
                'J' => 0,
                'T' => 10,
                'Q' => 12,
                'K' => 13,
                'A' => 14,
                _ => c as u8 - '0' as u8,
            })
            .collect::<Vec<u8>>();
        self.line1.push(Hand { card: card1, bid });
        self.line2.push(Hand { card: card2, bid });
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line1.sort();
        self.line1
            .iter()
            .enumerate()
            .map(|(i, p)| (i + 1) * p.bid)
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line2.sort();
        self.line2
            .iter()
            .enumerate()
            .map(|(i, p)| (i + 1) * p.bid)
            .sum()
    }
}
