//! <https://adventofcode.com/2019/day/14>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::collections::HashMap,
};

type ChemicalUnit = (String, usize);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<(Vec<ChemicalUnit>, ChemicalUnit)>,
}

fn parse_chemical_unit(s: &str) -> Result<ChemicalUnit, ParseError> {
    let parser = regex!(r"^(\d+) ([A-Z]+)");
    let segment = parser.captures(s).ok_or(ParseError)?;
    Ok((segment[2].to_string(), segment[1].parse::<usize>()?))
}

#[derive(Debug, Default, Eq, PartialEq)]
struct Resource<'a> {
    requirements: &'a [ChemicalUnit],
    amount: usize,
}

#[aoc(2019, 14)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^((\d+ [A-Z]+, )*)(\d+ [A-Z]+) => (\d+ [A-Z]+)");
        let segment = parser.captures(block).ok_or(ParseError)?;
        let mut vec = segment[1]
            .split(", ")
            .filter(|seg| !seg.is_empty())
            .map(|seg| parse_chemical_unit(seg).unwrap())
            .collect::<Vec<ChemicalUnit>>();
        vec.push(parse_chemical_unit(&segment[3])?);
        self.line.push((vec, parse_chemical_unit(&segment[4])?));
        Ok(())
    }
    fn wrap_up(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let hash = self.make_hash();
        dbg!(&hash.keys().count());
        let mut bag: HashMap<&str, usize> = HashMap::new();
        let mut extra: HashMap<&str, usize> = HashMap::new();
        bag.insert("FUEL", 1);
        let mut num_ore: usize = 0;
        while let Some((key, amount)) = bag.iter().next() {
            let k: &str = *key;
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
                let num_repeat: usize = (amount + requires.amount - 1) / requires.amount;
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
        dbg!(&hash.keys().count());
        let mut range = (1, 100_000_000_000);
        while 1 < range.1 - range.0 {
            let trying = (range.1 + range.0) / 2;
            let mut bag: HashMap<&str, usize> = HashMap::new();
            let mut extra: HashMap<&str, usize> = HashMap::new();
            bag.insert("FUEL", trying);
            let mut num_ore: usize = 0;
            while let Some((key, amount)) = bag.iter().next() {
                let k: &str = *key;
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
                    let num_repeat: usize = (amount + requires.amount - 1) / requires.amount;
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
        dbg!(&range);
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
