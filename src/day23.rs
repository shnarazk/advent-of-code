#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        collections::{HashMap, VecDeque},
        io::{stdin, Read},
    },
};

pub fn day23(part: usize, flag: String) {
    assert!(flag.starts_with('-'));
    let sample = vec![3, 8, 9, 1, 2, 5, 4, 6, 7];
    let test = vec![3, 6, 2, 9, 8, 1, 7, 5, 4];
    if part == 1 {
        if flag == "-test" {
            dbg!(part1(9, 100, &sample));
            assert_eq!(part1(9, 100, &sample), "67384529");

        } else {
            dbg!(part1(9, 100, &test));
        }
    } else {
        if flag == "-test" {
            dbg!(part2(1_000_000, 10_000_000, &sample));
            assert_eq!(part2(1_000_000, 10_000_000, &sample), 149245887792);
        } else {
            dbg!(part2(1_000_000, 10_000_000, &test));
        }
    }
}

#[derive(Debug, PartialEq)]
struct Config1 {
    cups: VecDeque<usize>,
    highest: usize,
    lowest: usize,
}

impl Config1 {
    fn from(v: Vec<usize>) -> Config1 {
        let mut cups = VecDeque::new();
        for n in v.iter() {
            cups.push_back(*n);
        }
        Config1 {
            cups,
            highest: *v.iter().max().unwrap(),
            lowest: *v.iter().min().unwrap(),
        }
    }
    fn shift(&mut self) -> usize {
        let val = self.cups.pop_front().unwrap();
        self.cups.push_back(val);
        val
    }
    fn shift_back(&mut self) -> usize {
        let val = self.cups.pop_back().unwrap();
        self.cups.push_front(val);
        val
    }
    fn round(&mut self) {
        let current_cup = self.shift();
        let mut pick_ups = Vec::new();
        pick_ups.push(self.cups.pop_front().unwrap());
        pick_ups.push(self.cups.pop_front().unwrap());
        pick_ups.push(self.cups.pop_front().unwrap());

        let mut destination = if current_cup == self.lowest {
                self.highest
        } else {
                current_cup - 1
        };
        while pick_ups.contains(&destination) {
            if destination == self.lowest {
                destination = self.highest;
            } else {
                destination -= 1;
            }
        }
        // shift to clear up to destination
        while self.cups[0] != destination {
            self.shift();
        }
        self.shift();
        // push back pick ups
        for n in pick_ups.iter().rev() {
            self.cups.push_front(*n);
        }
        // shift back to current cup
        while self.cups[0] != current_cup {
            self.shift_back();
        }
        self.shift();
    }
    /*
    fn round1(&mut self) {
        let Config1 {
            ref mut cups,
            ref mut workplace,
            highest,
            lowest,
            ref mut rotate,
        } = self;
        let current_cup = cups.pop_front().unwrap();
        let mut pick_ups = Vec::new();
        pick_ups.push(cups.pop_front().unwrap());
        pick_ups.push(cups.pop_front().unwrap());
        pick_ups.push(cups.pop_front().unwrap());

        let mut destination = current_cup;
        while !cups.contains(&destination) {
            if destination == *lowest {
                destination = *highest;
            } else {
                destination -= 1;
            }
        }
        workplace.clear();
        workplace.push_back(current_cup);
        for n in cups.iter() {
            workplace.push_back(*n);
            if *n == destination {
                for m in pick_ups.iter() {
                    workplace.push_back(*m);
                }
            }
        }
        // shift
        while workplace[0] != current_cup {
            let n = workplace.pop_front().unwrap();
            workplace.push_back(n);
            *rotate += 1;
        }
        let n = workplace.pop_front().unwrap();
        workplace.push_back(n);
        *rotate += 1;
        std::mem::swap(workplace, cups);
        self.workplace.clear();
    }
     */
    fn answer(&mut self) -> String {
        // unrole
        while self.cups[0] != 1 {
            let n = self.cups.pop_front().unwrap();
            self.cups.push_back(n);
        }
        let mut result: String = String::new();
        for i in 1..self.cups.len() {
            result.push_str(&format!("{}", self.cups[i]));
        }
        result
    }
    fn answer2(&self) -> usize {
        for i in 1..self.cups.len() {
            if self.cups[i] == 1 {
                return self.cups[i + 1] * self.cups[i + 2]
            }
        }
        0
    }
}

#[derive(Debug, PartialEq)]
struct Config {
    next_cup: Vec<usize>,
    highest: usize,
}

impl Config {
    fn new(n: usize, init: &[usize]) -> Config {
        let mut next_cup: Vec<usize> = Vec::new();
        for i in 0..=n {
            next_cup.push(i + 1);
        }
        for i in 1..init.len() {
            next_cup[init[i - 1]] = init[i];
        }
        // dbg!(&next_cup[1..]);

        if init.len() < n {
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
            highest: n,
        }
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

fn part1(ncup: usize, nround: usize, vec: &[usize]) -> String {
    let mut conf = Config::new(ncup, &vec);
    let mut current = vec[0];
    for n in 0..nround {
        current = conf.round(current);
    }
    conf.answer1()
}

fn part2(ncup: usize, nround: usize, vec: &[usize]) -> usize {
    let mut conf = Config::new(ncup, &vec);
    let mut current = vec[0];
    for n in 0..nround {
        current = conf.round(current);
    }
    conf.answer2()
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
