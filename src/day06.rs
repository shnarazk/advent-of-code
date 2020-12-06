#![allow(dead_code)]
#![allow(unused_variables)]
use {
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        collections::{HashMap, HashSet},
        io::{self, Read},
    },
};

fn main() {
    let mut buffer = String::new();
    io::stdin()
        .read_to_string(&mut buffer)
        .expect("something wrong");

    let mut nvalids = 0;

    for g in buffer.split("\n\n") {
        let mut dic: HashMap<char, usize> = HashMap::new();
        let mut n = 0;
        for p in g.split('\n') {
            if 0 < p.len() {
                n += 1;
            }
            for a in p.chars() {
                if 'a' <= a && a <= 'z' {
                    let k = dic.entry(a).or_insert(0);
                    *k += 1;
                }
            }
        }
        let x = dic.iter().filter(|(k, m)| **m == n).count();
        dbg!((x, n, &dic));
        nvalids += x
    }
    dbg!(nvalids);
}

fn part1() {
    let mut buffer = String::new();
    io::stdin()
        .read_to_string(&mut buffer)
        .expect("something wrong");

    let mut nvalids = 0;

    for g in buffer.split("\n\n") {
        let mut dic: HashSet<char> = HashSet::new();
        for p in g.split('\n') {
            for a in p.chars() {
                if 'a' <= a && a <= 'z' {
                    dic.insert(a);
                }
            }
        }
        nvalids += dic.len();
        dbg!(&dic);
    }
    dbg!(nvalids);
}

