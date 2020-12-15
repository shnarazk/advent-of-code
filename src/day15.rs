#![allow(dead_code)]
#![allow(unused_variables)]
use std::{
    collections::HashMap,
    io::{stdin, Read},
};

fn at(p: (usize, usize)) -> usize {
    p.1
}

fn count(p: (usize, usize)) -> usize {
    p.0
}

fn diff(p: (usize, usize)) -> usize {
    if p.0 < p.1 {
        p.1 - p.0
    } else {
        p.0 - p.1
    }
}

fn main() {
    let mut buf = String::new();
    stdin().read_to_string(&mut buf).expect("wrong");

    let mut dic: HashMap<usize, usize> = HashMap::new();
    // let mut nvalids = 0;
    let mut vec: Vec<usize> = Vec::new();
    let mut last = 0;

    let mut clock = 0;
    let mut iter = buf.split(',');
    let mut ch = iter.next();
    loop {
        if let Some(c) = ch {
            if let Ok(n) = c.trim().parse::<usize>() {
                ch = iter.next();
                clock += 1;
                if ch.is_some() {
                    let entry = dic.entry(n).or_insert(0);
                    *entry = clock;
                    // println!("Turn {}: call.{}, a starting number", clock, n);
                } else {
                    // println!("Turn {}: call.{}, a starting number", clock, n);
                    last = n;
                    break;
                }
            }
        }
    }
    clock += 1;
    loop {
        let last_entry = dic.entry(last).or_insert(0);
        if *last_entry == 0 {
            *last_entry = clock - 1;
            // println!("Turn {}: call.0, {} is a first spoken, set {}", clock, last, clock - 1);
            last = 0;
        } else {
            // println!("Turn {}: call.{}, {} is spoken at.{} set {}", clock, clock - 1 - *last_entry, last, *last_entry, clock - 1);
            last = clock - 1 - *last_entry;
            *last_entry = clock - 1;
        }
        clock += 1;

        // part 1
        // if 2020 < clock {
        //     panic!("done as {}", last);
        // }

        //part 2
        if 30000000 < clock {
            panic!("done as {}", last);
        }
    }
}
