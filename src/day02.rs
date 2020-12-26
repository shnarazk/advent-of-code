use {
    lazy_static::lazy_static,
    regex::Regex,
    std::io::{self, Read},
};

pub fn day02() {
    let mut buffer = String::new();
    io::stdin().read_to_string(&mut buffer).expect("something wrong");
    println!("{}", buffer.lines().map(|s| check_line2(s)).sum::<usize>());
}

fn check_line1(str: &str) -> usize {
    lazy_static! {
        static ref PARSER: Regex = Regex::new(r"^([0-9]+)-([0-9]+) ([a-zA-Z]): (.*)$").expect("wrong regex");
    }
    if let Some(m) = PARSER.captures(str) {
        let mi = m[1].parse::<usize>().unwrap();
        let ma = m[2].parse::<usize>().unwrap();
        let target: char = m[3].chars().next().unwrap();
        println!("min:{}, max:{}, letter:{}, body: {}", mi, ma, target, &m[4]);
        let occ = m[4].chars().filter(|c| *c == target).count();
        (mi <= occ && occ <= ma) as usize
    } else {
        0
    }
}

fn check_line2(str: &str) -> usize {
    lazy_static! {
        static ref PARSER: Regex = Regex::new(r"^([0-9]+)-([0-9]+) ([a-zA-Z]): (.*)$").expect("wrong regex");
    }
    if let Some(m) = PARSER.captures(str) {
        let pos1 = m[1].parse::<usize>().unwrap();
        let pos2 = m[2].parse::<usize>().unwrap();
        let ch: char = m[3].chars().next().unwrap();
        let target: &str = &m[4];
        let p1 = target.chars().nth(pos1 - 1) == Some(ch);
        let p2 = target.chars().nth(pos2 - 1) == Some(ch);
        if p1 ^ p2 {
            println!("OK: p1:{}=>{}, p2:{}=>{}, letter:{}, body: {}",
                     pos1, target.chars().nth(pos1 - 1).unwrap(),
                     pos2, target.chars().nth(pos2 - 1).unwrap(),
                     ch, target);
        } else {
            println!("NG: p1:{}=>{}, p2:{}=>{}, letter:{}, body: {}",
                     pos1, target.chars().nth(pos1 - 1).unwrap(),
                     pos2, target.chars().nth(pos2 - 1).unwrap(),
                     ch, target);
        }
        (p1 ^ p2) as usize
    } else {
        0
    }
}
