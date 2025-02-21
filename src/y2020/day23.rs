//! <https://adventofcode.com/2020/day/23>
use crate::framework::{AdventOfCode, aoc_at};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    next_cup: Vec<usize>,
    start_from: usize,
    round_end: usize,
    highest: usize,
}

#[aoc_at(2020, 23)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = usize;
    fn part1(&mut self) -> String {
        let cups = vec![3, 6, 2, 9, 8, 1, 7, 5, 4];
        self.setup(9, 100, &cups);
        if 20 < self.next_cup.len() {
            return String::new();
        }
        self.turn_rounds().answer1()
    }
    fn part2(&mut self) -> usize {
        let cups = vec![3, 6, 2, 9, 8, 1, 7, 5, 4];
        self.setup(1_000_000, 10_000_000, &cups);
        self.turn_rounds().answer2()
    }
}

impl Puzzle {
    fn setup(&mut self, len: usize, nr: usize, init: &[usize]) {
        let mut next_cup: Vec<usize> = Vec::new();
        for i in 0..=len {
            next_cup.push(i + 1);
        }
        for i in 1..init.len() {
            next_cup[init[i - 1]] = init[i];
        }
        // dbg!(&next_cup[1..]);

        let last_of_init = init.last().unwrap();
        if init.len() < len {
            next_cup[*last_of_init] = init.len() + 1;
            let last = next_cup.len() - 1;
            next_cup[last] = init[0];
        } else {
            next_cup[*last_of_init] = init[0];
        }
        // dbg!(&next_cup[1..]);
        self.next_cup = next_cup;
        self.start_from = init[0];
        self.round_end = nr;
        self.highest = len;
    }
    fn round(&mut self, current: usize) -> usize {
        let pick1: usize = self.next_cup[current];
        let pick2: usize = self.next_cup[pick1];
        let pick3: usize = self.next_cup[pick2];
        let destination: usize = {
            let mut tmp = if current == 1 {
                self.highest
            } else {
                current - 1
            };
            while tmp == pick1 || tmp == pick2 || tmp == pick3 {
                tmp -= 1;
                if tmp == 0 {
                    tmp = self.highest;
                }
            }
            tmp
        };
        self.next_cup[current] = self.next_cup[pick3];
        let tmp2 = self.next_cup[destination];
        self.next_cup[destination] = pick1;
        self.next_cup[pick3] = tmp2;
        self.next_cup[current]
    }
    fn turn_rounds(&mut self) -> &mut Self {
        let mut current = self.start_from;
        for _ in 0..self.round_end {
            current = self.round(current);
        }
        self
    }
    fn answer1(&self) -> String {
        let mut i = 1;
        let mut s: String = String::new();
        while self.next_cup[i] != 1 {
            i = self.next_cup[i];
            s.push_str(&format!("{}", i));
        }
        s
    }
    fn answer2(&self) -> usize {
        let x = self.next_cup[1];
        let y = self.next_cup[x];
        x * y
    }
}
