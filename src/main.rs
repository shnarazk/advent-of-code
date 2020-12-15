#![allow(dead_code)]
#![allow(unused_variables)]
use std::io::{stdin, Read};

fn main() {
    let mut buf = String::new();
    stdin().read_to_string(&mut buf).expect("wrong");

    // let mut dic: HashMap<&str, &str> = HashMap::new();
    // let mut nvalids = 0;

    for c in buf.split('\n') {
        // for kv in c.split_ascii_whitespace() {
        //     let k_v = kv.split(':').collect::<Vec<_>>();
        //     dic.insert(k_v[0], k_v[1]);
        // }
    }
    // dbg!(nvalids);
}

fn valid(key: &str, _val: &str) -> bool {
    // lazy_static! { static ref RE: Regex = Regex::new(r"^(\d+)(cm|in)$").expect("wrong regex"); }
    // if let Some(m) = RE.captures(key) {}
    false
}

mod test {
    use super::*;
    #[test]
    fn test1() {
        assert_eq!(0, 0);
    }
}
