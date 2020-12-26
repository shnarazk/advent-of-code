use std::io::{self, Read};

pub fn day01() {
    let mut buffer = String::new();
    let mut v: Vec<usize> = Vec::new();
    io::stdin()
        .read_to_string(&mut buffer)
        .expect("something wrong");
    for s in buffer.lines() {
        v.push(s.parse::<usize>().expect("bad int"));
    }
    for i in &v {
        for j in &v {
            if i + j == 2020 {
                println!("{} * {} = {}", i, j, i * j)
            }
        }
    }
    for (i, x) in v.iter().enumerate() {
        for (j, y) in v.iter().enumerate().skip(i) {
            for z in v.iter().skip(j) {
                if x + y + z == 2020 {
                    println!("{} * {} * {} = {}", x, y, z, x * y * z);
                }
            }
        }
    }
}
