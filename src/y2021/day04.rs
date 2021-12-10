use crate::{AdventOfCode, Description, Maybe, ParseError};
use regex::Regex;
use std::borrow::Cow;

#[derive(Debug)]
struct Puzzle {
    hands: Vec<usize>,
    board: Vec<Vec<Vec<usize>>>,
    order: Vec<usize>,
    num_col: usize,
    num_row: usize,
}

fn col_at(vec: &[Vec<usize>], at: usize) -> Cow<Vec<usize>> {
    Cow::Owned(vec.iter().map(|l| l[at]).collect::<Vec<usize>>())
}

fn row_at(vec: &[Vec<usize>], at: usize) -> Cow<Vec<usize>> {
    Cow::Borrowed(&vec[at])
}

fn grade(vec: &[usize], order: &[usize], board: &[Vec<usize>]) -> Option<(usize, usize)> {
    let mut need = 0;
    for i in vec.iter() {
        if let Some(o) = order.get(*i) {
            need = need.max(*o);
        } else {
            return None;
        }
    }
    let point = board
        .iter()
        .map(|v| {
            v.iter()
                .map(|n| if order[*n] <= need { 0 } else { *n })
                .sum::<usize>()
        })
        .sum();
    Some((need, point))
}

impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = usize;
    const YEAR: usize = 2021;
    const DAY: usize = 4;
    const DELIMITER: &'static str = "\n\n";
    fn default() -> Self {
        Self {
            hands: Vec::new(),
            board: Vec::new(),
            order: Vec::new(),
            num_col: 5,
            num_row: 5,
        }
    }
    fn insert(&mut self, block: &str) -> Maybe<()> {
        let mut vec = Vec::new();
        for l in block.split('\n') {
            if l.is_empty() {
                break;
            }
            let line = l
                .split(' ')
                .filter(|s| !s.is_empty())
                .map(|n| n.parse::<usize>().expect("-"))
                .collect::<Vec<_>>();
            if !line.is_empty() {
                vec.push(line);
            }
        }
        self.board.push(vec);
        Ok(())
    }
    fn header(&mut self, input: String) -> Maybe<String> {
        let parser: Regex = Regex::new(r"^(.+)\n\n((.|\n)+)$").expect("wrong");
        let segment = parser.captures(&input).ok_or(ParseError)?;
        for num in segment[1].split(',') {
            self.hands.push(num.parse::<usize>()?);
        }
        Ok(segment[2].to_string())
    }
    fn after_insert(&mut self) {
        self.num_col = self.board[0][0].len();
        self.num_row = self.board[0].len();
        self.order = self.hands.clone();
        for (i, h) in self.hands.iter().enumerate() {
            self.order[*h] = i;
        }
    }
    fn part1(&mut self) -> usize {
        let x: Vec<(usize, usize)> = self
            .board
            .iter()
            .flat_map(|b| {
                (0..self.num_row)
                    .flat_map(|i| {
                        [
                            grade(&row_at(b, i), &self.order, b),
                            grade(&col_at(b, i), &self.order, b),
                        ]
                    })
                    .flatten()
                    .collect::<Vec<_>>()
            })
            .collect();
        let result = x.iter().min_by_key(|(h, _)| h).expect("??");
        dbg!(self.hands[result.0], result.1);
        self.hands[result.0] * result.1
    }
    fn part2(&mut self) -> usize {
        let x: Vec<(usize, usize)> = self
            .board
            .iter()
            .map(|b| {
                (0..self.num_row)
                    .flat_map(|i| {
                        [
                            grade(&row_at(b, i), &self.order, b),
                            grade(&col_at(b, i), &self.order, b),
                        ]
                    })
                    .flatten()
                    .min_by_key(|(h, _)| *h)
                    .expect("??")
            })
            .collect();
        let result = x.iter().max_by_key(|(h, _)| h).expect("??");
        dbg!(self.hands[result.0], result.1);
        self.hands[result.0] * result.1
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::solve(&desc, part));
}
