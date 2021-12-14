//! <https://adventofcode.com/2021/day/14>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    lazy_static::lazy_static,
    regex::Regex,
    std::collections::{HashMap, HashSet},
};

#[derive(Debug, Default)]
pub struct Puzzle {
    template: Vec<char>,
    line: Vec<(char, char, char)>,
    rule: HashMap<(char, char), char>,
    atom: HashSet<char>,
}

#[aoc(2021, 14)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        lazy_static! {
            static ref TEMPLATE: Regex = Regex::new(r"^([A-Z]+)$").expect("wrong");
            static ref RULE: Regex = Regex::new(r"^([A-Z])([A-Z]) -> ([A-Z])$").expect("wrong");
        }
        if let Ok(segment) = TEMPLATE.captures(block).ok_or(ParseError) {
            self.template = segment[1].chars().collect::<Vec<char>>();
        } else if let Ok(segment) = RULE.captures(block).ok_or(ParseError) {
            self.line.push((
                segment[1].chars().next().unwrap(),
                segment[2].chars().next().unwrap(),
                segment[3].chars().next().unwrap(),
            ));
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
        for (l, r, m) in self.line.iter() {
            self.rule.insert((*l, *r), *m);
            self.atom.insert(*l);
            self.atom.insert(*r);
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut now = self.template.clone();
        for _ in 0..10 {
            let mut next: Vec<char> = Vec::new();
            for p in now.windows(2) {
                // println!("{:?}", p);
                next.push(p[0]);
                if let Some(ch) = self.rule.get(&(p[0], p[1])) {
                    next.push(*ch);
                }
            }
            next.push(*now.last().unwrap());
            std::mem::swap(&mut now, &mut next);
        }
        let occurs = self
            .atom
            .iter()
            .map(|c| now.iter().filter(|d| c == *d).count())
            .collect::<Vec<usize>>();
        println!(
            "{:?}",
            now.iter()
                .map(|c| format!("{}", c))
                .collect::<Vec<String>>()
                .join("")
        );
        occurs.iter().max().unwrap() - occurs.iter().min().unwrap()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut now: HashMap<(char, char), usize> = HashMap::new();
        for v in self.template.windows(2) {
            now.insert((v[0], v[1]), 1);
        }
        // add sentinel
        now.insert((self.template[self.template.len() - 1], ' '), 1);
        for _ in 0..40 {
            let mut next: HashMap<(char, char), usize> = HashMap::new();
            for (p, n) in now.iter() {
                // println!("{:?}", p);
                if let Some(m) = self.rule.get(&(p.0, p.1)) {
                    *next.entry((p.0, *m)).or_insert(0) += n;
                    *next.entry((*m, p.1)).or_insert(0) += n;
                } else {
                    next.insert(*p, *n);
                }
            }
            std::mem::swap(&mut now, &mut next);
        }
        dbg!(&now);
        let occurs = self
            .atom
            .iter()
            .map(|c| {
                now.iter()
                    .map(|(p, d)| if *c == p.0 { *d } else { 0 })
                    .sum()
            })
            .collect::<Vec<usize>>();
        dbg!(&occurs);
        occurs.iter().max().unwrap() - occurs.iter().min().unwrap()
    }
}
