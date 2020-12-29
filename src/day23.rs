// #![allow(dead_code)]
use crate::{ProblemDescription, ProblemSolver};

pub fn day23(part: usize, desc: ProblemDescription) {
    let ncups = if part == 1 { 9 } else { 1_000_000 };
    let nround = if part == 1 { 100 } else { 10_000_000 };
    let cups = if desc == ProblemDescription::None {
        vec![3, 6, 2, 9, 8, 1, 7, 5, 4]
    } else {
        vec![3, 8, 9, 1, 2, 5, 4, 6, 7]
    };
    dbg!(Config::new(ncups, &cups).set_round(nround).run(part));
}


#[derive(Debug, PartialEq)]
struct Config {
    next_cup: Vec<usize>,
    start_from: usize,
    round_end: usize,
    highest: usize,
}

impl ProblemSolver<(), String, usize> for Config {
    const DAY: usize = 23;
    const DELIMITER: &'static str = "";
    fn default() -> Self {
        Config {
            next_cup: Vec::new(),
            start_from: 1,
            round_end: 0,
            highest: 1,
        }
    } 
    fn part1(&mut self) -> String {
        if 20 < self.next_cup.len() {
            return String::new();
        }
        let mut current = self.start_from;
        for _ in 0..self.round_end {
            current = self.round(current);
        }
        self.answer1()
    }
    fn part2(&mut self) -> usize {
        let mut current = self.start_from;
        for _ in 0..self.round_end {
            current = self.round(current);
        }
        self.answer2()
    }
}

impl Config {
    fn new(len: usize, init: &[usize]) -> Config {
        let mut next_cup: Vec<usize> = Vec::new();
        for i in 0..=len {
            next_cup.push(i + 1);
        }
        for i in 1..init.len() {
            next_cup[init[i - 1]] = init[i];
        }
        // dbg!(&next_cup[1..]);

        if init.len() < len {
            let last_of_init = init.last().unwrap();
            next_cup[*last_of_init] = init.len() + 1;
            let last = next_cup.len() - 1;
            next_cup[last] = init[0];
        } else {
            let last_of_init = init.last().unwrap();
            next_cup[*last_of_init] = init[0];
        }
        // dbg!(&next_cup[1..]);
        Config {
            next_cup,
            start_from: init[0],
            round_end: 0,
            highest: len,
        }
    }
    fn set_round(&mut self, nr: usize) -> &mut Self {
        self.round_end = nr;
        self
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


mod test {
    use super::*;
    #[test]
    fn test0() {
        let mut conf = Config::new(9, &vec![3, 8, 9, 1, 2, 5, 4, 6, 7]);
        let mut current = 3;
        dbg!(&conf);
        for _ in 0..10 {
            current = conf.round(current);
            dbg!(&conf);
        }
        assert_eq!(conf.answer1(), "92658374");
    }
    #[test]
    fn test1() {
        let mut conf = Config::new(9, &vec![3, 8, 9, 1, 2, 5, 4, 6, 7]);
        let mut current = 3;
        dbg!(&conf);
        for _ in 0..100 {
            current = conf.round(current);
            dbg!(&conf);
        }
        assert_eq!(conf.answer1(), "67384529");
    }
    #[test]
    fn test2() {
        let mut conf = Config::new(9, &vec![3, 6, 2, 9, 8, 1, 7, 5, 4]);
        let mut current = 3;
        dbg!(&conf);
        for _ in 0..100 {
            current = conf.round(current);
            dbg!(&conf);
        }
        assert_eq!(conf.answer1(), "24798635");
    }
}
