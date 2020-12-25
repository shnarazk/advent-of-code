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

fn main() {
    let mut buf = String::new();
    stdin().read_to_string(&mut buf).expect("wrong");
    read(&buf);
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
