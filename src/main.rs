#![allow(dead_code)]
#![allow(unused_variables)]
use {
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        collections::HashMap,
        io::{self, Read},
    },
};

fn main() {
    let mut buffer = String::new();
    io::stdin()
        .read_to_string(&mut buffer)
        .expect("something wrong");

    let mut dic: HashMap<&str, &str> = HashMap::new();
    let mut nvalids = 0;

    for c in buffer.split("\n") {
        for kv in c.split_ascii_whitespace() {
            let k_v = kv.split(':').collect::<Vec<_>>();
            dic.insert(k_v[0], k_v[1]);
        }
        nvalids += check_keys(&dic);
        dbg!((&dic, nvalids));
    }
    dbg!(nvalids);
}

fn check_keys(_dic: &HashMap<&str, &str>) -> usize {
    0
}

fn valid(key: &str, _val: &str) -> bool {
    lazy_static! {
        static ref RE: Regex = Regex::new(r"^(\d+)(cm|in)$").expect("wrong regex");
    }
    if let Some(m) = RE.captures(key) {}
    false
}
