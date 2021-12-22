//! <https://adventofcode.com/2015/day/19>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::collections::HashSet;
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser,
    },
    lazy_static::lazy_static,
    regex::Regex,
    std::collections::HashMap,
};

#[derive(Debug, Default)]
pub struct Puzzle {
    num_atom: usize,
    dic: HashMap<String, usize>,
    line: Vec<String>,
    rule: Vec<(String, Vec<String>)>,
}

fn parse_atoms(mut stream: Vec<String>, line: &str) -> Vec<String> {
    lazy_static! {
        static ref ATOM: Regex = Regex::new(r"^([A-Z][^A-Z]*)(.*)$").expect("wrong");
    }
    if let Some(segment) = ATOM.captures(line) {
        stream.push(segment[1].to_string());
        return parse_atoms(stream, &segment[2]);
    }
    stream
}

#[aoc(2015, 19)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    // fn header(&mut self, input: String) -> Result<Option<String>, ParseError> {
    //     let parser: Regex = Regex::new(r"^(.+)\n\n((.|\n)+)$").expect("wrong");
    //     let segment = parser.captures(input).ok_or(ParseError)?;
    //     for num in segment[1].split(',') {
    //         let _value = num.parse::<usize>()?;
    //     }
    //     Ok(Some(segment[2].to_string()))
    // }
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        lazy_static! {
            static ref RULE: Regex =
                Regex::new(r"^([A-Z][a-zA-Z]*) => ([A-Z][a-zA-Z]*)$").expect("wrong");
            static ref BIGBANG: Regex = Regex::new(r"^e => ([A-Z][a-zA-Z]*)$").expect("wrong");
            static ref STRING: Regex = Regex::new(r"^([A-Z][a-zA-Z]+)$").expect("wrong");
        }
        if let Some(segment) = RULE.captures(block) {
            let prec = parse_atoms(Vec::new(), &segment[1]);
            let post = parse_atoms(Vec::new(), &segment[2]);
            assert!(prec.len() == 1, "{:?}", prec);
            for w in prec.iter() {
                if !self.dic.contains_key(w) {
                    self.dic.insert(w.to_string(), self.num_atom);
                    self.num_atom += 1;
                }
            }
            for w in post.iter() {
                if !self.dic.contains_key(w) {
                    self.dic.insert(w.to_string(), self.num_atom);
                    self.num_atom += 1;
                }
            }
            self.rule.push((prec[0].to_string(), post));
        } else if let Some(segment) = BIGBANG.captures(block) {
            let post = parse_atoms(Vec::new(), &segment[1]);
            for w in post.iter() {
                if !self.dic.contains_key(w) {
                    self.dic.insert(w.to_string(), self.num_atom);
                    self.num_atom += 1;
                }
            }
            self.rule.push(("e".to_string(), post));
        } else if let Some(segment) = STRING.captures(block) {
            let string = parse_atoms(Vec::new(), &segment[0]);
            for w in string.iter() {
                if !self.dic.contains_key(w) {
                    self.dic.insert(w.to_string(), self.num_atom);
                    self.num_atom += 1;
                }
            }
            self.line = string;
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.rule);
        // dbg!(&self.line);
        // dbg!(&self.dic);
    }
    fn part1(&mut self) -> Self::Output1 {
        dbg!(&self.rule);
        let mut dic = Vec::new();
        dic.resize(self.num_atom, "");
        for (w, n) in self.dic.iter() {
            dic[*n] = w;
        }
        let rule = self
            .rule
            .iter()
            .map(|(atom, a)| {
                (
                    *self.dic.get(atom).unwrap(),
                    a.iter()
                        .map(|atom| *self.dic.get(atom).unwrap())
                        .collect::<Vec<usize>>(),
                )
            })
            .collect::<Vec<(usize, Vec<usize>)>>();
        let string = self
            .line
            .iter()
            .map(|s| *self.dic.get(s).unwrap())
            .collect::<Vec<usize>>();
        let mut bag: HashSet<Vec<usize>> = HashSet::new();
        bag.insert(string);
        let mut new_bag: HashSet<Vec<usize>> = HashSet::new();
        for st in bag.iter() {
            for (i, n) in st.iter().enumerate() {
                for (_, seq) in rule.iter().filter(|(key, _)| key == n) {
                    let mut new_string: Vec<usize> = st.clone();
                    new_string.remove(i);
                    for x in seq.iter().rev() {
                        new_string.insert(i, *x);
                    }
                    new_bag.insert(new_string);
                }
            }
        }
        for s in new_bag.iter() {
            println!(
                "{:?}",
                s.iter().map(|n| dic[*n]).collect::<Vec<&str>>().join("")
            );
        }
        new_bag.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.dic.insert("e".to_string(), self.num_atom);
        dbg!(self.line.len());
        dbg!(&self.rule.len());
        let mut to_mnemonic = Vec::new();
        to_mnemonic.resize(self.num_atom + 1, "");
        for (w, n) in self.dic.iter() {
            to_mnemonic[*n] = w;
        }
        let rule = self
            .rule
            .iter()
            .map(|(atom, a)| {
                (
                    *self.dic.get(atom).unwrap(),
                    a.iter()
                        .map(|atom| *self.dic.get(atom).unwrap())
                        .collect::<Vec<usize>>(),
                )
            })
            .collect::<Vec<(usize, Vec<usize>)>>();
        let medicine = self
            .line
            .iter()
            .map(|s| *self.dic.get(s).unwrap())
            .collect::<Vec<usize>>();
        dbg!((0..medicine.len())
            .filter(|i| rule.iter().any(|(atom, poly)| medicine[*i] == *atom))
            .count());
        let mut bag: HashSet<Vec<usize>> = HashSet::new();
        let mut new_bag: HashSet<Vec<usize>> = HashSet::new();
        bag.insert(vec![0]);
        for i in 1.. {
            for st in bag.iter() {
                for (i, n) in st.iter().enumerate() {
                    for (_, seq) in rule.iter().filter(|(key, _)| key == n) {
                        let mut new_string: Vec<usize> = st.clone();
                        new_string.remove(i);
                        for x in seq.iter().rev() {
                            new_string.insert(i, *x);
                        }
                        if new_string.starts_with(&medicine[..12]) {
                            dbg!(new_string
                                .iter()
                                .map(|n| to_mnemonic[*n])
                                .collect::<Vec<&str>>()
                                .join(""));
                            return i;
                        }
                        if new_string.len() < medicine.len() {
                            new_bag.insert(new_string);
                        }
                    }
                }
            }
            std::mem::swap(&mut bag, &mut new_bag);
            new_bag.clear();
        }
        for s in new_bag.iter() {
            println!(
                "{:?}",
                s.iter()
                    .map(|n| to_mnemonic[*n])
                    .collect::<Vec<&str>>()
                    .join("")
            );
        }
        new_bag.len()

        // let mut rule = self.rule.iter()
        //     .map(|(k, seq)| {
        //         let mut qes = seq.clone();
        //         qes.reverse();
        //         (qes, k)
        //     })
        //     .collect::<Vec<_>>();
        // rule.sort_unstable();
        // for r in rule.iter() {
        //     println!("{:?} => {}", r.0, r.1);
        // }
        // let mut med = self.line.clone();
        // med.reverse();
        // println!("{:?}", med.join(""));
    }
}

#[cfg(feature = "y2015")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    // #[test]
    // fn test_part1() {
    //     assert_eq!(
    //         Puzzle::solve(Description::TestData("".to_string()), 1),
    //         Answer::Part1(0)
    //     );
    // }
}
