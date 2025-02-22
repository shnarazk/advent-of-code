//! <https://adventofcode.com/2019/day/14>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashMap,
};

type ChemicalUnit = (String, usize);

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(Vec<ChemicalUnit>, ChemicalUnit)>,
}

#[derive(Debug, Default, Eq, PartialEq)]
struct Resource<'a> {
    requirements: &'a [ChemicalUnit],
    amount: usize,
}

mod parser {
    use {
        super::*,
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline, space1},
            combinator::{separated, seq},
        },
    };

    fn parse_chemical_unit(s: &mut &str) -> ModalResult<ChemicalUnit> {
        seq!(parse_usize, _: space1, alpha1)
            .map(|(n, s): (usize, &str)| (s.to_string(), n))
            .parse_next(s)
    }

    fn parse_line(s: &mut &str) -> ModalResult<(Vec<ChemicalUnit>, ChemicalUnit)> {
        seq!(
            separated(1.., parse_chemical_unit, ", "),
            _: " => ",
            parse_chemical_unit
        )
        .parse_next(s)
    }
    pub fn parse(s: &mut &str) -> ModalResult<Vec<(Vec<ChemicalUnit>, ChemicalUnit)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2019, 14)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let hash = self.make_hash();
        let mut bag: HashMap<&str, usize> = HashMap::new();
        let mut extra: HashMap<&str, usize> = HashMap::new();
        bag.insert("FUEL", 1);
        let mut num_ore: usize = 0;
        while let Some((key, amount)) = bag.iter().next() {
            let k: &str = key;
            let mut amount = *amount;
            bag.remove(k);
            if let Some(requires) = hash.get(k) {
                if let Some(remains) = extra.get(k) {
                    if amount <= *remains {
                        *extra.entry(k).or_insert(0) -= amount;
                        continue;
                    } else {
                        amount -= remains;
                        extra.remove(k);
                    }
                }
                let num_repeat: usize = amount.div_ceil(requires.amount);
                for (name, amnt) in requires.requirements {
                    if name == "ORE" {
                        // println!("- {} ORE to produce {amount} {k}", amnt * num_repeat);
                        num_ore += amnt * num_repeat;
                    } else {
                        // println!("- {} {name} for {amount} {k}", amnt * num_repeat);
                        *bag.entry(name).or_insert(0) += amnt * num_repeat;
                    }
                }
                let remains = requires.amount * num_repeat - amount;
                let entry = extra.entry(k).or_insert(0);
                *entry += remains;
            }
        }
        num_ore
    }
    fn part2(&mut self) -> Self::Output2 {
        let max_ore = 1_000_000_000_000;
        let hash = self.make_hash();
        let mut range = (1, 100_000_000_000);
        while 1 < range.1 - range.0 {
            let trying = (range.1 + range.0) / 2;
            let mut bag: HashMap<&str, usize> = HashMap::new();
            let mut extra: HashMap<&str, usize> = HashMap::new();
            bag.insert("FUEL", trying);
            let mut num_ore: usize = 0;
            while let Some((key, amount)) = bag.iter().next() {
                let k: &str = key;
                let mut amount = *amount;
                bag.remove(k);
                if let Some(requires) = hash.get(k) {
                    if let Some(remains) = extra.get(k) {
                        if amount <= *remains {
                            *extra.entry(k).or_insert(0) -= amount;
                            continue;
                        } else {
                            amount -= remains;
                            extra.remove(k);
                        }
                    }
                    let num_repeat: usize = amount.div_ceil(requires.amount);
                    for (name, amnt) in requires.requirements {
                        if name == "ORE" {
                            // println!("- {} ORE to produce {amount} {k}", amnt * num_repeat);
                            num_ore += amnt * num_repeat;
                        } else {
                            // println!("- {} {name} for {amount} {k}", amnt * num_repeat);
                            *bag.entry(name).or_insert(0) += amnt * num_repeat;
                        }
                    }
                    let remains = requires.amount * num_repeat - amount;
                    let entry = extra.entry(k).or_insert(0);
                    *entry += remains;
                }
            }
            if max_ore < num_ore {
                range.1 = trying;
            } else {
                range.0 = trying;
            }
            // dbg!(&range);
        }
        range.0
    }
}

impl Puzzle {
    fn make_hash<'a>(&'a self) -> HashMap<&'a str, Resource<'a>> {
        let mut hash: HashMap<&'a str, Resource<'a>> = HashMap::new();
        for (vec, (c, u)) in self.line.iter() {
            hash.insert(
                c,
                Resource {
                    requirements: vec,
                    amount: *u,
                },
            );
        }
        hash
    }
}
