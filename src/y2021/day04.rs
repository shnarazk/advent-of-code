#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::{AdventOfCode, Description, FromDataFile, ParseError, Maybe};
use lazy_static::lazy_static;
use regex::Regex;
use std::collections::HashMap;

type DataSegment = Vec<Vec<usize>>;

impl FromDataFile for DataSegment {
    fn parse(s: &str) -> Result<Self, ParseError> {
        let mut vec = Vec::new();
        for l in s.split('\n') {
            if l.is_empty() {
                break;
            }
            let line = l.split(' ').filter(|s| !s.is_empty()).map(|n| n.parse::<usize>().expect("-")).collect::<Vec<_>>();
            if !line.is_empty() {
                vec.push(line);
            }
        }
        Ok(vec)
    }
}

#[derive(Debug, PartialEq)]
struct Puzzle {
    hands: Vec<usize>,
    board: Vec<DataSegment>,
    order: Vec<usize>,
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
    let point = board.iter().map(|v| v.iter().map(|n| if order[*n] <= need { 0 } else { *n } ).sum::<usize>() ).sum();
    Some((need, point))
}

impl AdventOfCode<DataSegment, usize, usize> for Puzzle {
    const YEAR: usize = 2021;
    const DAY: usize = 4;
    const DELIMITER: &'static str = "\n\n";
    fn default() -> Self {
        Self {
            hands: Vec::new(),
            board: Vec::new(),
            order: Vec::new(),
        }
    }
    fn insert(&mut self, object: DataSegment) {
        self.board.push(object);
    }
    fn parse(desc: Description) -> Maybe<Self> {
        let mut instance = Self::default();
        let input = Self::load(desc)?;
        let mut iter = input.split(Self::DELIMITER); 
        for num in iter.next().ok_or(ParseError)?.split(',') {
            instance.hands.push(num.parse::<usize>()?);
        }
        for block in iter {
            instance.insert(DataSegment::parse(block)?);
        }
        instance.order = instance.hands.clone(); 
        for (i, h) in instance.hands.iter().enumerate() {
            instance.order[*h] = i;
        }
        // dbg!(&instance);
        Ok(instance)
    }

    fn part1(&mut self) -> usize {
        let nrow = self.board[0].len();
        let ncol = self.board[0][0].len();
        let x: Vec<(usize, usize)> = self.board.iter()
            .flat_map(|b|
                      (0..nrow)
                      .flat_map(|i|
                                [
                                    grade(&b[i], &self.order, b),
                                    grade(&b.iter().map(|l| l[i]).collect::<Vec<usize>>(), &self.order, b),
                                ]
                      )
                      .flatten()
                      .collect::<Vec<_>>())
            .collect();
        let result = x.iter().min_by_key(|(h, v)| h).expect("??");
        dbg!(self.hands[result.0], result.1);
        self.hands[result.0] * result.1
    }
    fn part2(&mut self) -> usize {
        let nrow = self.board[0].len();
        let ncol = self.board[0][0].len();
        let x: Vec<(usize, usize)> = self.board.iter()
            .map(|b|
                 (0..nrow).flat_map(|i|
                               [
                                   grade(&b[i], &self.order, b),
                                   grade(&b.iter().map(|l| l[i]).collect::<Vec<usize>>(), &self.order, b),
                               ]
                 )
                 .flatten()
                 .min_by_key(|(h, v)| *h).expect("??"))
            .collect();
        dbg!(&x);
        let result = x.iter().max_by_key(|(h, v)| h).expect("??");
        dbg!(self.hands[result.0], result.1);
        self.hands[result.0] * result.1
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::parse(desc).expect("-").run(part));
}
