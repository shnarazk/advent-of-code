use {lazy_static::lazy_static, regex::Regex, std::collections::HashMap};

pub fn day04(_part: usize, buffer: String) {
    let mut nvalids = 0;
    for c in buffer.split("\n\n") {
        let mut dic: HashMap<&str, &str> = HashMap::new();
        for kv in c.split_ascii_whitespace() {
            let k_v = kv.split(':').collect::<Vec<_>>();
            dic.insert(k_v[0], k_v[1]);
        }
        nvalids += check_keys(&dic);
        // dbg!((&dic, nvalids));
    }
    dbg!(nvalids);
}

fn check_keys(dic: &HashMap<&str, &str>) -> usize {
    let keys = vec!["byr", "iyr", "eyr", "hgt", "hcl", "ecl", "pid"];
    let mut count = 0;
    for key in &keys {
        if let Some(val) = dic.get(key) {
            if valid(key, val) {
                count += 1;
            } else {
                dbg!((key, val));
            }
        }
    }
    (keys.len() == count) as usize
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
