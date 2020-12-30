use crate::{Description, ProblemObject, ProblemSolver};
use {lazy_static::lazy_static, regex::Regex, std::collections::HashMap};

pub fn day04(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

#[derive(Debug, PartialEq)]
struct Rule {
    dic: HashMap<String, String>,
}

const KEYS: [&str; 7] = ["byr", "iyr", "eyr", "hgt", "hcl", "ecl", "pid"];

impl ProblemObject for Rule {
    fn parse(s: &str) -> Option<Self> {
        let mut dic: HashMap<String, String> = HashMap::new();
        for kv in s.split_ascii_whitespace() {
            let k_v = kv.split(':').collect::<Vec<_>>();
            dic.insert(k_v[0].to_string(), k_v[1].to_string());
        }
        Some(Rule { dic })
    }
}

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
            if let Some(val) = self.dic.get(&key.to_string()) {
                if valid(key, val) {
                    count += 1;
                } else {
                    dbg!((key, val));
                }
            }
        }
        KEYS.len() == count
    }
}

#[derive(Debug, PartialEq)]
struct Setting {
    entry: Vec<Rule>,
}

impl ProblemSolver<Rule, usize, usize> for Setting {
    const DAY: usize = 4;
    const DELIMITER: &'static str = "\n\n";
    fn default() -> Self {
        Setting { entry: Vec::new() }
    }
    fn insert(&mut self, rule: Rule) {
        self.entry.push(rule);
    }
    fn part1(&mut self) -> usize {
        self.entry.iter().filter(|r| r.check_keys()).count()
    }
    fn part2(&mut self) -> usize {
        self.entry.iter().filter(|r| r.check_values()).count()
    }
}

fn valid(key: &str, val: &str) -> bool {
    lazy_static! {
        static ref HIGHT: Regex = Regex::new(r"^(\d+)(cm|in)$").expect("wrong regex");
        static ref HAIR: Regex = Regex::new(r"^#[0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]$")
            .expect("wrong regex");
        static ref EYE: Regex =
            Regex::new(r"^(amb|blu|brn|gry|grn|hzl|oth)$").expect("wrong regex");
        static ref PID: Regex = Regex::new(r"^\d{9}$").expect("wrong regex");
    }
    match key {
        "byr" => {
            if let Ok(y) = val.parse::<usize>() {
                return 1920 <= y && y <= 2002;
            }
        }
        "iyr" => {
            if let Ok(y) = val.parse::<usize>() {
                return 2010 <= y && y <= 2020;
            }
        }
        "eyr" => {
            if let Ok(y) = val.parse::<usize>() {
                return 2020 <= y && y <= 2030;
            }
        }
        "hgt" => {
            if let Some(m) = HIGHT.captures(val) {
                if m[2] == *"cm" {
                    if let Ok(v) = m[1].parse::<usize>() {
                        return 150 <= v && v <= 193;
                    }
                } else if m[2] == *"in" {
                    if let Ok(v) = m[1].parse::<usize>() {
                        return 59 <= v && v <= 76;
                    }
                }
            }
        }
        "hcl" => {
            return HAIR.captures(val).is_some();
        }
        "ecl" => {
            return EYE.captures(val).is_some();
        }
        "pid" => {
            return PID.captures(val).is_some();
        }
        _ => (),
    }
    false
}

#[cfg(test)]
mod test {
    use {
        super::*,
        crate::{Answer, Description},
    };
    #[test]
    fn test_part1() {
        const TEST: &str = "\
ecl:gry pid:860033327 eyr:2020 hcl:#fffffd
byr:1937 iyr:2017 cid:147 hgt:183cm

iyr:2013 ecl:amb cid:350 eyr:2023 pid:028048884
hcl:#cfa07d byr:1929

hcl:#ae17e1 iyr:2013
eyr:2024
ecl:brn pid:760753108 byr:1931
hgt:179cm

hcl:#cfa07d eyr:2025 pid:166559648
iyr:2011 ecl:brn hgt:59in";
        assert_eq!(
            Setting::parse(Description::TestData(TEST.to_string())).run(1),
            Answer::Part1(2)
        );
    }
    #[test]
    fn test_part2_invalid() {
        const TEST: &str = "\
eyr:1972 cid:100
hcl:#18171d ecl:amb hgt:170 pid:186cm iyr:2018 byr:1926

iyr:2019
hcl:#602927 eyr:1967 hgt:170cm
ecl:grn pid:012533040 byr:1946

hcl:dab227 iyr:2012
ecl:brn hgt:182cm pid:021572410 eyr:2020 byr:1992 cid:277

hgt:59cm ecl:zzz
eyr:2038 hcl:74454a iyr:2023
pid:3556412378 byr:2007";
        assert_eq!(
            Setting::parse(Description::TestData(TEST.to_string())).run(2),
            Answer::Part2(0)
        );
    }
    #[test]
    fn test_part2_valid() {
        const TEST: &str = "\
pid:087499704 hgt:74in ecl:grn iyr:2012 eyr:2030 byr:1980
hcl:#623a2f

eyr:2029 ecl:blu cid:129 byr:1989
iyr:2014 pid:896056539 hcl:#a97842 hgt:165cm

hcl:#888785
hgt:164cm byr:2001 iyr:2015 cid:88
pid:545766238 ecl:hzl
eyr:2022

iyr:2010 hgt:158cm hcl:#b6652a ecl:blu byr:1944 eyr:2021 pid:093154719";
        assert_eq!(
            Setting::parse(Description::TestData(TEST.to_string())).run(2),
            Answer::Part2(4)
        );
    }
}
