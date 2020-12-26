#![allow(dead_code)]
#![allow(unused_variables)]
use std::io::{self, Read};

pub fn day10() {
    let mut buffer = String::new();
    io::stdin()
        .read_to_string(&mut buffer)
        .expect("something wrong");

    let mut vec: Vec<usize> = Vec::new();
    vec.push(0);

    for c in buffer.split("\n") {
        if c.is_empty() {
            break;
        }
        if let Ok(n) = c.parse::<usize>() {
            vec.push(n);
        } else {
            panic!("wrong number");
        }
    }
    vec.sort_unstable();
    // dbg!(&vec);
    let mut diff1 = 0;
    let mut diff3 = 0;
    for i in 1..vec.len() {
        match vec[i] - vec[i - 1] {
            1 => diff1 += 1,
            3 => diff3 += 1,
            _ => panic!("wrong"),
        }
    }
    diff3 += 1;
    assert_eq!(vec.len(), diff1 + diff3);
    dbg!((diff1, diff3, diff1 * diff3));
    let mx = *vec.last().unwrap();
    let mut count: Vec<usize> = Vec::new();
    count.push(1);
    for _ in 0..mx {
        count.push(0);
    }
    for n in &vec[1..] {
        count[*n] += count[*n - 1];
        if 2 <= *n {
            count[*n] += count[*n - 2];
        }
        if 3 <= *n {
            count[*n] += count[*n - 3];
        }
    }
    dbg!(count.last());
}
