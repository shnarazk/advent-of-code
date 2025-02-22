//! <https://adventofcode.com/2020/day/4>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashMap,
};

#[derive(Clone, Debug, PartialEq)]
struct Rule {
    dic: HashMap<String, String>,
}

const KEYS: [&str; 7] = ["byr", "iyr", "eyr", "hgt", "hcl", "ecl", "pid"];

impl Rule {
    fn check_keys(&self) -> bool {
        KEYS.iter().all(|key| self.dic.contains_key(*key))
    }
    fn check_values(&self) -> bool {
        KEYS.iter().all(|key| {
            self.dic
                .get(key.to_owned())
                .is_some_and(|val| parser::valid(key, val))
        })
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    entry: Vec<Rule>,
}

mod parser {
    use {
        crate::parser::{parse_dec, parse_usize},
        winnow::{
            ModalResult, Parser,
            combinator::{alt, repeat, seq},
            token::one_of,
        },
    };
    fn hexletter(s: &mut &str) -> ModalResult<char> {
        one_of(('a'..='z', '0'..='9')).parse_next(s)
    }

    fn parse_hight<'a>(s: &'a mut &str) -> ModalResult<(usize, &'a str)> {
        seq!(parse_usize, alt(("cm", "in"))).parse_next(s)
    }

    fn parse_hair(s: &mut &str) -> ModalResult<Vec<char>> {
        seq!(_: '#', repeat(6, hexletter))
            .map(|(s,)| s)
            .parse_next(s)
    }

    fn parse_eye<'a>(s: &'a mut &str) -> ModalResult<&'a str> {
        alt(("amb", "blu", "brn", "gry", "grn", "hzl", "oth")).parse_next(s)
    }

    fn parse_pid(s: &mut &str) -> ModalResult<usize> {
        repeat(9, parse_dec)
            .map(|v: Vec<usize>| v.iter().fold(0, |acc, x| acc * 10 + x))
            .parse_next(s)
    }

    pub fn valid(key: &str, mut val: &str) -> bool {
        match key {
            "byr" => val
                .parse::<usize>()
                .is_ok_and(|y| (1920..=2002).contains(&y)),
            "iyr" => val
                .parse::<usize>()
                .is_ok_and(|y| (2010..=2020).contains(&y)),
            "eyr" => val
                .parse::<usize>()
                .is_ok_and(|y| (2020..=2030).contains(&y)),
            "hgt" => parse_hight(&mut val).is_ok_and(|(m, u)| {
                if u == "cm" {
                    (150..=193).contains(&m)
                } else if u == "in" {
                    (59..=76).contains(&m)
                } else {
                    unreachable!()
                }
            }),
            "hcl" => val.len() == 7 && parse_hair(&mut val).is_ok(),
            "ecl" => val.len() == 3 && parse_eye(&mut val).is_ok(),
            "pid" => val.len() == 9 && parse_pid(&mut val).is_ok(),
            _ => unreachable!(),
        }
    }
}

#[aoc(2020, 4)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input
            .split("\n\n")
            .map(|l| l.trim())
            .filter(|l| !l.is_empty())
        {
            let mut dic: HashMap<String, String> = HashMap::new();
            for kv in l.split_ascii_whitespace() {
                let k_v = kv.split(':').collect::<Vec<_>>();
                dic.insert(k_v[0].to_string(), k_v[1].to_string());
            }
            self.entry.push(Rule { dic });
        }
        Ok(())
    }
    fn part1(&mut self) -> usize {
        self.entry.iter().filter(|r| r.check_keys()).count()
    }
    fn part2(&mut self) -> usize {
        self.entry
            .iter()
            .filter(|r| r.check_keys())
            .filter(|r| r.check_values())
            .count()
    }
}
