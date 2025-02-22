//! <https://adventofcode.com/2020/day/22>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::{
        cmp::Ordering,
        collections::{HashSet, VecDeque},
    },
};

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

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{separated, seq},
        },
    };

    fn parse_player(s: &mut &str) -> ModalResult<Vec<usize>> {
        seq!(
            _: "Player ",
            _: parse_usize,
            _: ":\n",
            separated(1.., parse_usize, newline),
        )
        .map(|(s,)| s)
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Vec<usize>>> {
        separated(2..=2, parse_player, (newline, newline)).parse_next(s)
    }
}

#[aoc(2020, 22)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        let mut v = parser::parse(&mut input)?;
        self.player2 = VecDeque::from(v.pop().unwrap());
        self.player1 = VecDeque::from(v.pop().unwrap());
        Ok(())
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
