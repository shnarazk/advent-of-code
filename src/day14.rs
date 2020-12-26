#![allow(dead_code)]
#![allow(unused_variables)]
use {
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        collections::HashMap,
        io::{stdin, Read},
    },
};

#[derive(Debug, PartialEq)]
enum OP {
    Mask(usize, usize, Vec<usize>),
    Set(usize, usize),
}

impl OP {
    fn apply1_to(&self, v: usize) -> usize {
        if let OP::Mask(zs, os, _) = self {
            (v | os) & !zs
        } else {
            v
        }
    }
    fn apply2_to(&self, v: usize) -> Vec<usize> {
        if let OP::Mask(_, os, ms) = self {
            let base = v | os;
            let mut vec = Vec::new();
            for mut i in 0..2_i32.pow(ms.len() as u32) as usize {
                let mut addr = base;
                for loc in ms.iter() {
                    addr &= !(1 << loc);
                    addr |= (i % 2) << loc;
                    i /= 2;
                }
                vec.push(addr);
            }
            vec
        } else {
            vec![v]
        }
    }
}

pub fn day14() {
    let mut buf = String::new();
    stdin().read_to_string(&mut buf).expect("wrong");

    let mut dic: HashMap<usize, usize> = HashMap::new();
    // let mut nvalids = 0;

    let mut mask = OP::Mask(0, 0, Vec::new());
    for c in buf.split('\n') {
        if let Some(op) = parse(c) {
            // dbg!(&op);
            match op {
                OP::Mask(_, _, _) => {
                    mask = op;
                }
                OP::Set(a, v) => {
                    // let entry = dic.entry(a).or_insert(0);
                    // *entry = mask.apply1_to(v);
                    // dbg!((v, &mask, *entry));
                    for addr in mask.apply2_to(a).iter() {
                        let entry = dic.entry(*addr).or_insert(0);
                        *entry = v;
                        // dbg!((addr, v));
                    }
                }
            }
        }
    }
    dbg!(&dic);
    dbg!(dic.values().sum::<usize>());
}

fn parse(str: &str) -> Option<OP> {
    lazy_static! {
        static ref MASK: Regex = Regex::new(r"^mask = ((X|0|1)+)").expect("wrong");
        static ref SET: Regex = Regex::new(r"^mem\[(\d+)\] = (\d+)").expect("wrong");
    }
    if let Some(m) = MASK.captures(str) {
        let zeros = m[1]
            .chars()
            .fold(0, |sum, letter| sum * 2 + if letter == '0' { 1 } else { 0 });
        let ones = m[1]
            .chars()
            .fold(0, |sum, letter| sum * 2 + if letter == '1' { 1 } else { 0 });
        let wilds = m[1]
            .chars()
            .enumerate()
            .fold(Vec::new(), |mut v, (i, letter)| {
                if letter == 'X' {
                    v.push(35 - i);
                    v
                } else {
                    v
                }
            });
        return Some(OP::Mask(zeros, ones, wilds));
    }
    if let Some(m) = SET.captures(str) {
        let address = m[1].parse::<usize>().unwrap();
        let val = m[2].parse::<usize>().unwrap();
        return Some(OP::Set(address, val));
    }
    None
}
