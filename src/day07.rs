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

fn most_outer_of(links: &HashSet<(String, String, usize)>, origin: &str, outers: &mut HashSet<String>) {
    for (from, to, _) in links {
        if to == origin {
            outers.insert(from.to_string());
            most_outer_of(links, &from, outers);
        }
    }
}

fn collects(links: &HashSet<(String, String, usize)>, origin: &str) -> usize {
    let mut count = 0;
    for (from, to, n) in links {
        if from == origin {
            count += n * collects(links, &to);
        }
    }
    count + 1
}


pub fn day07() {
    let mut buffer = String::new();
    io::stdin()
        .read_to_string(&mut buffer)
        .expect("something wrong");

    let mut links: HashSet<(String, String, usize)> = HashSet::new();

    for c in buffer.split("\n") {
        parse(&mut links, c);
    }
    let mut outers: HashSet<String> = HashSet::new();
    most_outer_of(&links, "shiny gold", &mut outers);
    dbg!(outers.len());
    dbg!(collects(&links, "shiny gold") - 1);
}

fn parse(dic: &mut HashSet<(String, String, usize)>, line: &str) {
    lazy_static! {
        static ref HEAD: Regex = Regex::new(r"^([a-z]+ [a-z]+) bags? contain (.*)").expect("wrong");
        static ref PREP: Regex = Regex::new(r"(\d+) ([a-z]+ [a-z]+) bags?(, (.*))?").expect("wrong");
    }
    if let Some(head) = HEAD.captures(line) {
        let mut b: String = head[2].to_string();
        while let Some(prep) = PREP.captures(&b) {
            dic.insert((head[1].to_string(), prep[2].to_string(), prep[1].parse::<usize>().unwrap()));
            if let Some(rest) = prep.get(4) {
                b = rest.as_str().to_string();
                if b == "." {
                    break;
                }
            } else {
                break;
            } 
        }
    }
}
