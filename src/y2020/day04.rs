//! <https://adventofcode.com/2020/day/4>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
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
                if valid(key, val) {
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

#[aoc(2020, 4)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
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

fn valid(key: &str, val: &str) -> bool {
    let hight = regex!(r"^(\d+)(cm|in)$");
    let hair = regex!(r"^#[0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]$");
    let eye = regex!(r"^(amb|blu|brn|gry|grn|hzl|oth)$");
    let pid = regex!(r"^\d{9}$");
    match key {
        "byr" => {
            if let Ok(y) = val.parse::<usize>() {
                return (1920..=2002).contains(&y);
            }
        }
        "iyr" => {
            if let Ok(y) = val.parse::<usize>() {
                return (2010..=2020).contains(&y);
            }
        }
        "eyr" => {
            if let Ok(y) = val.parse::<usize>() {
                return (2020..=2030).contains(&y);
            }
        }
        "hgt" => {
            if let Some(m) = hight.captures(val) {
                if m[2] == *"cm" {
                    if let Ok(v) = m[1].parse::<usize>() {
                        return (150..=193).contains(&v);
                    }
                } else if m[2] == *"in" {
                    if let Ok(v) = m[1].parse::<usize>() {
                        return (59..=76).contains(&v);
                    }
                }
            }
        }
        "hcl" => {
            return hair.captures(val).is_some();
        }
        "ecl" => {
            return eye.captures(val).is_some();
        }
        "pid" => {
            return pid.captures(val).is_some();
        }
        _ => (),
    }
    false
}
