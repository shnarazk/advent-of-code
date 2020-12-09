#![allow(dead_code)]
#![allow(unused_variables)]
use {
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        collections::HashSet,
        io::{self, Read},
    },
};

fn main() {
    let mut buffer = String::new();
    io::stdin()
        .read_to_string(&mut buffer)
        .expect("something wrong");

    let mut vec: Vec<usize> = Vec::new();

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
/* part 1
    // dbg!(&vec);
    let len = 25;
    let mut set: HashSet<usize> = HashSet::new();
    for n in &vec[..len] {
        set.insert(*n);
    }
    for (i, n) in vec.iter().enumerate().skip(len) {
        let out = vec[i - len];
        /*
        let mn = *vec[i - len..i].iter().min().expect("?");
        let mx = *vec[i - len..i].iter().max().expect("?");
        // easy check
        if 2 * mx < *n || *n < 2 * mn {
            panic!("easy found: {} @ {} (min: {}, max: {})", *n, i, mn, mx);
        }
        */
        // exhaustive check
        let mut found = false;
        for k in &set {
            if 2 * *k < *n {
                if set.contains(&(*n - *k)) {
                    found = true;
                    break;
                }
            }
        }
        if found {
            set.remove(&out);
            assert!(!set.contains(&out));
            if !set.insert(*n) {
                panic!("this requires HashMap");
            }
            assert!(set.contains(&n));
            println!("out {}, in {}", out, *n);
        } else {
            dbg!(&set);
            panic!("hard found: {} @ {}", *n, i);
        }
    }
*/
    let len = vec.len();
    let magic_number = 85848519;
    'next: for start in 0..len {
        let mut sum = 0;
        for i in start..len {
            sum += vec[i];
            if sum == magic_number {
                let mn = *vec[start..i].iter().min().unwrap();
                let mx = *vec[start..i].iter().max().unwrap();
                panic!("found a sequence starting from {} to {}, ans: {}", start, i, mn + mx);
            }
            if magic_number < sum {
                continue 'next;
            }
        }
    }

}

fn valid(key: &str, _val: &str) -> bool {
    lazy_static! {
        static ref RE: Regex = Regex::new(r"^(\d+)(cm|in)$").expect("wrong regex");
    }
    if let Some(m) = RE.captures(key) {}
    false
}
