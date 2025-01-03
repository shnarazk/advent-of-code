//! <https://adventofcode.com/2020/day/22>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::{
        cmp::Ordering,
        collections::{HashSet, VecDeque},
    },
};

fn parse(block: &str) -> Option<VecDeque<usize>> {
    let head = regex!(r"^Player (\d+):");
    if head.captures(block).is_some() {
        let mut q: VecDeque<usize> = VecDeque::new();
        for l in block.split('\n').skip(1) {
            if l.is_empty() {
                break;
            }
            q.push_back(l.parse::<usize>().expect("panic"));
        }
        return Some(q);
    }
    None
}

type Player = VecDeque<usize>;
type Config = (Player, Player);

#[derive(Clone, Debug, Default, PartialEq)]
struct Cache {
    set: HashSet<Config>,
}

impl Cache {
    fn saw(&mut self, player1: &Player, player2: &Player) -> Option<usize> {
        if self.set.contains(&(player1.clone(), player2.clone())) {
            return Some(1);
        }
        if self.set.contains(&(player2.clone(), player1.clone())) {
            return Some(2);
        }
        let len = self.set.len();
        self.set.insert((player1.clone(), player2.clone()));
        debug_assert!(self.set.contains(&(player1.clone(), player2.clone())));
        debug_assert_eq!(len + 1, self.set.len());
        None
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    player1: Player,
    player2: Player,
    cache: Cache,
}

#[aoc(2020, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n\n";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn parse(&mut self, buffer: String) -> Result<String, ParseError> {
        let mut iter = buffer.split(Self::DELIMITER);
        if let Some(text) = iter.next() {
            if let Some(element) = parse(text) {
                self.player1 = element;
            }
        }
        if let Some(text) = iter.next() {
            if let Some(element) = parse(text) {
                self.player2 = element;
            }
        }
        Ok("".to_string())
    }
    fn part1(&mut self) -> usize {
        let mut stopper = None;
        while self.check_winner(stopper).is_none() {
            stopper = self.round_part1();
            // println!(
            //     " 1 -> {:?}\n 2 -> {:?}\n {} cached, stopper: {:?}",
            //     &self.player1,
            //     &self.player2,
            //     self.cache.set.len(),
            //     stopper
            // );
        }
        let mut score = 0;
        if let Some(p) = self.check_winner(stopper) {
            // println!(
            //     "found winner {}: {:?} {:?}",
            //     p, &self.player1, &self.player2
            // );
            let v = if p == 1 { &self.player1 } else { &self.player2 };
            for (i, h) in v.iter().rev().enumerate() {
                score += (i + 1) * *h;
                // println!("{} * {} = {} => {}, ", *h, i + 1, (i + 1) * *h, score);
            }
        }
        score
    }
    fn part2(&mut self) -> usize {
        let mut stopper = None;
        while self.check_winner(stopper).is_none() {
            stopper = self.round_part2();
        }
        let mut score = 0;
        if let Some(p) = self.check_winner(stopper) {
            // println!(
            //     "found winner {}: {:?} {:?}",
            //     p, &self.player1, &self.player2
            // );
            let v = if p == 1 { &self.player1 } else { &self.player2 };
            for (i, h) in v.iter().rev().enumerate() {
                score += (i + 1) * *h;
            }
        }
        score
    }
}

impl Puzzle {
    fn check_winner(&self, exception: Option<usize>) -> Option<usize> {
        if exception.is_some() {
            return exception;
        }
        if self.player2.is_empty() {
            return Some(1);
        } else if self.player1.is_empty() {
            return Some(2);
        }
        None
    }
    fn round_part1(&mut self) -> Option<usize> {
        if let Some(h1) = self.player1.pop_front() {
            if let Some(h2) = self.player2.pop_front() {
                match h1.cmp(&h2) {
                    Ordering::Less => {
                        self.player2.push_back(h2);
                        self.player2.push_back(h1);
                        // println!("Player2 won with {} against {}", h2, h1);
                    }
                    Ordering::Equal => panic!("equals!"),
                    Ordering::Greater => {
                        self.player1.push_back(h1);
                        self.player1.push_back(h2);
                        // println!("Player1 won with {} against {}", h1, h2);
                    }
                }
                // println!("Player1: {:?}", self.player1);
                // println!("Player2: {:?}", self.player2);
                None
            } else {
                self.player1.push_front(h1);
                Some(1)
            }
        } else {
            Some(2)
        }
    }
    fn round_part2(&mut self) -> Option<usize> {
        if self.player1.is_empty() {
            return Some(2);
        }
        if self.player2.is_empty() {
            return Some(1);
        }
        if let Some(x) = self.cache.saw(&self.player1, &self.player2) {
            return Some(x);
        }
        if let Some(p1_head) = self.player1.pop_front() {
            if let Some(p2_head) = self.player2.pop_front() {
                let append_to_p1: bool = {
                    if p1_head <= self.player1.len() && p2_head <= self.player2.len() {
                        let mut child = Puzzle {
                            player1: self.player1.clone(),
                            player2: self.player2.clone(),
                            ..Default::default()
                        };
                        child.player1.truncate(p1_head);
                        child.player2.truncate(p2_head);
                        // println!(
                        //     "{:>width$}",
                        //     ">",
                        //     width = child.player1.len() + child.player2.len()
                        // );
                        let mut stopper = None;
                        while child.check_winner(stopper).is_none() {
                            stopper = child.round_part2();
                        }
                        child.check_winner(stopper).expect("impossible") == 1
                    } else {
                        p2_head < p1_head
                    }
                };
                if append_to_p1 {
                    self.player1.push_back(p1_head);
                    self.player1.push_back(p2_head);
                } else {
                    self.player2.push_back(p2_head);
                    self.player2.push_back(p1_head);
                }
            }
        }
        None
    }
}
