#![allow(dead_code)]
#![allow(unused_variables)]
use std::io::{self, Read};

pub fn day05() {
    let mut buffer = String::new();
    io::stdin()
        .read_to_string(&mut buffer)
        .expect("something wrong");

    let mut max_sid = 0;
    let mut seats = [0; 128 * 8 + 1];

    for code in buffer.split('\n') {
        if code.is_empty() { break; }
        let (row_code, col_code) = code.split_at(7);
        let row = row_code.chars().map(|c| (c == 'B') as usize).collect::<Vec<_>>();
        let col = col_code.chars().map(|c| (c == 'R') as usize).collect::<Vec<_>>();
        let r = row.iter().fold(0, |t, n| t * 2 + n);
        let c = col.iter().fold(0, |t, n| t * 2 + n);
        let sid = r * 8 + c;
        dbg!((&code, r, c, sid));
        seats[sid] = 1;
        if max_sid < sid {
            max_sid = sid;
        }
    }
    dbg!(max_sid);
    for (i, e) in seats.iter().enumerate() {
        if *e == 0 && 7 < i && i < 126 * 8 {
            dbg!(i);
        }
    }
}
