//! <https://adventofcode.com/2020/day/4>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Clone, Debug, PartialEq)]
struct Rule {
    dic: HashMap<String, String>,
}

const KEYS: [&str; 7] = ["byr", "iyr", "eyr", "hgt", "hcl", "ecl", "pid"];

impl Rule {
    fn check_keys(&self) -> bool {
        self.dic
            .keys()
            .filter(|k| KEYS.contains(&k.as_str()))
            .count()
            == 7
    }
    fn check_values(&self) -> bool {
        let mut count = 0;
        for key in &KEYS {
            if let Some(val) = self.dic.get(key.to_owned()) {
                if parser::valid(key, val) {
                    count += 1;
                } else {
                    // dbg!((key, val));
                }
            }
        }
        KEYS.len() == count
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
            combinator::{alt, repeat, seq},
            token::one_of,
            ModalResult, Parser,
        },
    };
    fn hexletter(s: &mut &str) -> ModalResult<char> {
        one_of(('a'..='z', '0'..='9')).parse_next(s)
    }

    fn parse_hight<'a>(s: &'a mut &str) -> ModalResult<(usize, &'a str)> {
        seq!(parse_usize, alt(("cm", "in"))).parse_next(s)
    }

    fn parse_hair(s: &mut &str) -> ModalResult<Vec<char>> {
        seq!(_:"#", repeat(5..=5, hexletter))
            .map(|(s,)| s)
            .parse_next(s)
    }

    fn parse_eye<'a>(s: &'a mut &str) -> ModalResult<&'a str> {
        alt(("amb", "blu", "brn", "gry", "grn", "hzl", "oth")).parse_next(s)
    }

    fn parse_pid(s: &mut &str) -> ModalResult<usize> {
        repeat(9..=9, parse_dec)
            .map(|v: Vec<usize>| v.iter().fold(0, |acc, x| acc * 10 + x))
            .parse_next(s)
    }

    pub fn valid(key: &str, val: &str) -> bool {
        let s = val.to_string();
        match key {
            "byr" => val
                .parse::<usize>()
                .map_or_else(|_| false, |y| (1920..=2002).contains(&y)),
            "iyr" => val
                .parse::<usize>()
                .map_or_else(|_| false, |y| (2010..=2020).contains(&y)),
            "eyr" => val
                .parse::<usize>()
                .map_or_else(|_| false, |y| (2020..=2030).contains(&y)),
            "hgt" => parse_hight(&mut s.as_str()).map_or_else(
                |_| false,
                |(m, u)| {
                    if u == "cm" {
                        (150..=193).contains(&m)
                    } else if u == "in" {
                        (59..=76).contains(&m)
                    } else {
                        unreachable!()
                    }
                },
            ),
            "hcl" => parse_hair(&mut s.as_str()).is_ok(),
            "ecl" => parse_eye(&mut s.as_str()).is_ok(),
            "pid" => parse_pid(&mut s.as_str()).is_ok(),
            _ => unreachable!(),
        }
    }
}

#[aoc(2020, 4)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n\n";
    fn parse_block(&mut self, block: &str) -> Result<(), ParseError> {
        let mut dic: HashMap<String, String> = HashMap::new();
        for kv in block.split_ascii_whitespace() {
            let k_v = kv.split(':').collect::<Vec<_>>();
            dic.insert(k_v[0].to_string(), k_v[1].to_string());
        }
        self.entry.push(Rule { dic });
        Ok(())
    }
    fn part1(&mut self) -> usize {
        self.entry.iter().filter(|r| r.check_keys()).count()
    }
    fn part2(&mut self) -> usize {
        self.entry.iter().filter(|r| r.check_values()).count()
    }
}
