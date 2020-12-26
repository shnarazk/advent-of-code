use std::collections::{HashMap, HashSet};

pub fn day06(part: usize, buffer: String) {
    if part == 1 {
        part1(buffer);
    } else {
        part2(buffer);
    }
}

pub fn part2(buffer: String) {
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
        let x = dic.iter().filter(|(_, m)| **m == n).count();
        dbg!((x, n, &dic));
        nvalids += x
    }
    dbg!(nvalids);
}

fn part1(buffer: String) {
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
