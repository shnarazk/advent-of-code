#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        collections::HashMap,
        io::{stdin, Read},
    },
};

pub fn day16() {
    let mut buf = String::new();
    stdin().read_to_string(&mut buf).expect("wrong");
    solve(&buf);
}

type Range = (String, usize, usize, usize, usize);

fn solve(body: &str) {
    let mut dic: Vec<Range> = Vec::new();
    let mut samples: Vec<Vec<usize>> = Vec::new();
    let mut ticket: Vec<usize> = Vec::new();
    let mut field_cands: Vec<Vec<&Range>> = Vec::new();
    let mut good_samples: Vec<&[usize]> = Vec::new();

    let mut phase = 0;
    for l in body.split('\n') {
        match l {
            "your ticket:" => {
                phase += 1;
            }
            "nearby tickets:" => {
                phase += 1;
            }
            "" => (),
            _ if phase == 0 => {
                if let Some(r) = parse_range(l) {
                    dic.push(r);
                }
            }
            _ if phase == 1 => {
                ticket = parse_sample(l);
            }
            _ if phase == 2 => {
                samples.push(parse_sample(l));
            }
            _ => (),
        }
    }

    // build cands
    for field in &ticket {
        let mut res: Vec<&Range> = Vec::new();
        for pair in &dic {
            if valid(pair, *field) {
                res.push(pair);
            }
        }
        field_cands.push(res);
    }
    // dbg!(&field_cands);
    let mut count = 0;
    for v in &samples {
        let mut ok = true;
        for (i, e) in v.iter().enumerate() {
            if let Some(n) = invalid(&field_cands[i], *e) {
                println!("{}th element {} is out of range {:?}", i, e, &field_cands[i]);
                count += n;
                ok = false;
            }
        }
        if ok {
            println!("is good");
            good_samples.push(v);
        }
    }
    dbg!(count);

    let mut result: Vec<Vec<(String, usize)>> = Vec::new();
    for (i, ranges) in field_cands.iter().enumerate() {
        let mut valids: Vec<(String, usize)> = Vec::new();
        for range in ranges {
            if good_samples.iter().all(|sample| valid(range, sample[i])) {
                valids.push((range.0.clone(), ticket[i]));
            }
        }
        println!("{}-th field ({}) has {} cands: {:?}", i, ticket[i], valids.len(),
                 valids.iter().map(|r| &r.0).collect::<Vec<_>>(),
        );
        result.push(valids);
    }

    // simplify
    let mut trimmed: Vec<(String, usize)> = Vec::new();
    loop {
        let mut modified = false;
        let mut index: Option<usize> = None;
        for (i, cands) in result.iter().enumerate() {
            if cands.len() == 1 {
                index = Some(i);
                break;
            }
        }
        if let Some(n) =index {
            let name: String = result[n][0].0.clone();
            trimmed.push(result[n][0].clone());
            println!("asserted {}", name);
            for (j, v) in result.iter_mut().enumerate() {
                let old_len = v.len();
                v.retain(|range| range.0 != name);
                if v.len() != old_len {
                    modified = true;
                }
            }
        } else if !modified {
            break;
        }
    }
    // println!("{:?}", &trimmed);
    let mut count = 1;
    for r in &trimmed {
        if r.0.contains("departure") {
            println!("{}:\t{}", r.0, r.1);
            count *= r.1;
        }
    }
    panic!("done: {}", count);
}

fn valid((_, a, b, c, d): &Range, val: usize) -> bool {
    (*a <= val && val <= *b) || (*c <= val && val <= *d)
}

fn invalid(dic: &[&Range], x: usize) -> Option<usize> {
    if dic.iter().any(|(_, a, b, c, d)| (*a <= x && x <= *b) || (*c <= x && x <= *d)) {
        None
    } else {
        Some(x)
    }
}

fn parse_range(str: &str) -> Option<Range> {
    lazy_static! {
        static ref LINE: Regex = Regex::new(r"^([a-z ]+): (\d+)-(\d+) or (\d+)-(\d+)$").expect("wrong");
    }
    if let Some(m) = LINE.captures(str) {
        if let Ok(a) = m[2].parse::<usize>() {
            if let Ok(b) = m[3].parse::<usize>() {
                if let Ok(c) = m[4].parse::<usize>() {
                    if let Ok(d) = m[5].parse::<usize>() {
                        return Some((m[1].to_string(), a, b, c, d));
                    }
                }
            }
        }
    }
    None
}

fn parse_sample(str: &str) -> Vec<usize> {
    let mut vec: Vec<usize> = Vec::new();
    for s in str.split(',') {
        if let Ok(a) = s.parse::<usize>() {
            vec.push(a)
        }
    }
    vec
}

mod test {
    use super::*;
    const TEST1: &str = "\
class: 1-3 or 5-7
row: 6-11 or 33-44
seat: 13-40 or 45-50

your ticket:
7,1,14

nearby tickets:
7,3,47
40,4,50
55,2,20
38,6,12";
    #[test]
    fn test1() {
        solve(TEST1);
        panic!("");
    }
}
