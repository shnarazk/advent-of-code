#![allow(dead_code)]
#![allow(unused_variables)]
use std::io::{stdin, Read};

pub fn day13() {
    let mut buf = String::new();
    stdin().read_to_string(&mut buf).expect("wrong");

    let mut vec: Vec<(usize, usize)> = Vec::new();
    let mut iter = buf.split('\n');
    let time = iter.next().unwrap().parse::<usize>().unwrap();
    dbg!(time);
    let mut wait = usize::MAX;
    // let mut best = 0;
    for (i, b) in iter.next().unwrap().split(',').enumerate() {
        if let Ok(n) = b.parse::<usize>() {
            vec.push((n, i));
            let before = time % n;
            // if before == 0 {
            //    panic!("found: {}", 0);
            // }
            let w = n - before;
            if w < wait {
                wait = w;
                // best = n;
            }
        }
    }
    // dbg!(&vec);
    let mut x = vec[0];
    for tuple in vec.iter().skip(1) {
        let offset = if tuple.1 <= tuple.0 {
            tuple.0 - tuple.1
        } else {
            println!("逆転{}, {}", tuple.0, tuple.1);
            (tuple.0 * tuple.1 - tuple.1) % tuple.0
        };
        println!("周期{}で{}余る", tuple.0, offset);
        x = chinese(x, (tuple.0, offset));
        dbg!(x);
        //assert_eq!(tuple.0 - x.1 % tuple.0, tuple.1);
    }
    panic!("found {}", x.1);
}

/// Return `x` such that:
/// * x `mod` aq = am
/// * x `mod` bq = bm
///
/// ```
/// let a = chinese((3, 2), (5, 3));
/// assert_eq!(a.1, 8);
/// let b = chinese(a, (2, 7);
/// assert_eq!(b.1, 23);
/// ```
fn chinese((aq, ar): (usize, usize), (bq, br): (usize, usize)) -> (usize, usize) {
    let n = solve1(aq, bq);
    let nar = (n * ar) % bq;
    let nbr = (n * br) % bq;
    let m = if nar < nbr {
        nbr - nar
    } else {
        (bq + nbr) - nar
    };
    (aq * bq, aq * m + ar)
}

/// Return `X` such that:
/// (X * a) `mod` m = ((X * b) `mod` m) + 1
///
fn solve1(a: usize, m: usize) -> usize {
    for i in 0.. {
        if (i * a) % m == 1 {
            return i;
        }
    }
    panic!("can't");
}

fn lcm(a: usize, b: usize) -> usize {
    a * b / gcd(a, b)
}

fn gcd(a: usize, b: usize) -> usize {
    if a % b == 0 {
        b
    } else {
        gcd(b, a % b)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_lcm() {
        assert_eq!(lcm(3, 10), 30);
        assert_eq!(lcm(3, 8), 24);
        assert_eq!(lcm(3, 9), 9);
        assert_eq!(lcm(1, 11), 11);
        assert_eq!(lcm(280, 5928), 207480);
    }
    #[test]
    fn test_chinese() {
        let a = chinese((3, 2), (5, 3));
        assert_eq!(a.1, 8);
        let c = chinese(a, (2, 7));
        assert_eq!(c.1, 23);
    }
}
