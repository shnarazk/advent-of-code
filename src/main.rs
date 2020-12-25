#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        collections::HashMap,
        io::{stdin, Read},
    },
};

struct Encrypter {
    loop_size: usize,
    subject_number: usize,
}

fn pull_back(pub_key: usize, stage: usize) -> Option<usize> {
    let mut n = pub_key;
    if Encrypter::transform_aux(n / 7, stage, 7) == pub_key {
        return Some(n / 7);
    } else {
        return None;
    }
}

impl Encrypter {
    fn new(loop_size: usize) -> Encrypter {
        Encrypter {
            loop_size,
            subject_number: 7,
        }
    }
    fn transform(loop_size: usize, subject_number: usize) -> usize {
        let mut value = 1;
        for _ in 0..loop_size {
            value = (value * subject_number) % 20201227;
        }
        value
    }
    fn transform_aux(mut value: usize, loop_size: usize, subject_number: usize) -> usize {
        for _ in 0..loop_size {
            value = (value * subject_number) % 20201227;
        }
        value
    }
    fn determine_loop_size(public_key: usize) -> usize {
        let mut value = 1;
        for i in 1.. {
            value = (value * 7) % 20201227;
            if value == public_key {
                return i
            }
        }
        0
    }
}

fn main() {
    /*
    let card_pubkey = 5764801;
    let door_pubkey = 17807724;
    assert_eq!(Encrypter::transform(8, 7), card_pubkey);
    assert_eq!(Encrypter::transform(11, 7), door_pubkey);

    let card_loop_size = Encrypter::determine_loop_size(card_pubkey);
    let door_loop_size = Encrypter::determine_loop_size(door_pubkey);

    let encryption_key_by_card = Encrypter::transform(card_loop_size, door_pubkey);
    let encryption_key_by_door = Encrypter::transform(door_loop_size, card_pubkey);
    dbg!(encryption_key_by_card);
    dbg!(encryption_key_by_door);

    assert_eq!(encryption_key_by_card, encryption_key_by_door);
     */

    let card_pubkey = 12320657;
    let door_pubkey = 9659666;
    let card_loop_size = Encrypter::determine_loop_size(card_pubkey);
    let door_loop_size = Encrypter::determine_loop_size(door_pubkey);
    assert_eq!(Encrypter::transform(card_loop_size, 7), card_pubkey);
    assert_eq!(Encrypter::transform(door_loop_size, 7), door_pubkey);

    dbg!((card_loop_size, door_loop_size));
    let encryption_key_by_card = Encrypter::transform(card_loop_size, door_pubkey);
    let encryption_key_by_door = Encrypter::transform(door_loop_size, card_pubkey);
    dbg!(encryption_key_by_card);
    dbg!(encryption_key_by_door);

    assert_eq!(encryption_key_by_card, encryption_key_by_door);
}

fn read(buf: &str) -> usize {
    // let mut dic;
    for l in buf.split('\n') {
        // l.split_ascii_whitespace()
        if let Some(d) = parse(l) {
            // let k_v = kv.split(':').collect::<Vec<_>>();
            // dic.insert(d);
        }
    }
    eval()
}

fn parse(line: &str) -> Option<bool> {
    // lazy_static! { static ref RE: Regex = Regex::new(r"^(\d+)$").expect("error"); }
    // if let Some(m) = RE.captures(line) {}
    Some(false)
}

fn eval() -> usize {
    0
}

mod test {
    use super::*;
    const TEST1: &str = "\
";
    #[test]
    fn test1() {
        assert_eq!(read(TEST1), 1);
    }
}
