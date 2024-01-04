//! <https://adventofcode.com/2020/day/16>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

type Range = (String, usize, usize, usize, usize);

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    dic: Vec<Range>,
    samples: Vec<Vec<usize>>,
    ticket: Vec<usize>,
    field_cands: Vec<Vec<Range>>,
    good_samples: Vec<Vec<usize>>,
}

#[aoc(2020, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n\n";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn header(&mut self, body: String) -> Result<String, ParseError> {
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
                        self.dic.push(r);
                    }
                }
                _ if phase == 1 => {
                    self.ticket = parse_sample(l);
                }
                _ if phase == 2 => {
                    self.samples.push(parse_sample(l));
                }
                _ => (),
            }
        }
        // build cands
        for field in &self.ticket {
            let mut res: Vec<Range> = Vec::new();
            for pair in &self.dic {
                if valid(pair, *field) {
                    res.push(pair.clone());
                }
            }
            self.field_cands.push(res);
        }
        Ok("".to_string())
    }
    fn part1(&mut self) -> usize {
        // dbg!(&field_cands);
        let mut count = 0;
        for v in &self.samples {
            let mut ok = true;
            for (i, e) in v.iter().enumerate() {
                if let Some(n) = invalid(&self.field_cands[i], *e) {
                    println!(
                        "{}th element {} is out of range {:?}",
                        i, e, &self.field_cands[i]
                    );
                    count += n;
                    ok = false;
                }
            }
            if ok {
                println!("is good");
                self.good_samples.push(v.clone());
            }
        }
        count
    }
    fn part2(&mut self) -> usize {
        self.part1();
        let mut result: Vec<Vec<(String, usize)>> = Vec::new();
        for (i, ranges) in self.field_cands.iter().enumerate() {
            let mut valids: Vec<(String, usize)> = Vec::new();
            for range in ranges {
                if self
                    .good_samples
                    .iter()
                    .all(|sample| valid(range, sample[i]))
                {
                    valids.push((range.0.clone(), self.ticket[i]));
                }
            }
            println!(
                "{}-th field ({}) has {} cands: {:?}",
                i,
                self.ticket[i],
                valids.len(),
                valids.iter().map(|r| &r.0).collect::<Vec<_>>(),
            );
            result.push(valids);
        }
        // simplify
        let mut trimmed: Vec<(String, usize)> = Vec::new();
        loop {
            let mut index: Option<usize> = None;
            for (i, cands) in result.iter().enumerate() {
                if cands.len() == 1 {
                    index = Some(i);
                    break;
                }
            }
            if let Some(n) = index {
                let name: String = result[n][0].0.clone();
                trimmed.push(result[n][0].clone());
                println!("asserted {}", name);
                for v in result.iter_mut() {
                    v.retain(|range| range.0 != name);
                }
            } else {
                break;
            }
        }
        let mut count = 1;
        for r in &trimmed {
            if r.0.contains("departure") {
                println!("{}:\t{}", r.0, r.1);
                count *= r.1;
            }
        }
        count
    }
}

fn valid((_, a, b, c, d): &Range, val: usize) -> bool {
    (*a <= val && val <= *b) || (*c <= val && val <= *d)
}

fn invalid(dic: &[Range], x: usize) -> Option<usize> {
    if dic
        .iter()
        .any(|(_, a, b, c, d)| (*a <= x && x <= *b) || (*c <= x && x <= *d))
    {
        None
    } else {
        Some(x)
    }
}

fn parse_range(str: &str) -> Option<Range> {
    let line = regex!(r"^([a-z ]+): (\d+)-(\d+) or (\d+)-(\d+)$");
    if let Some(m) = line.captures(str) {
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
