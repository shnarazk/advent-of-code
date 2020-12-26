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

pub fn day19() {
    let mut buf = String::new();
    stdin().read_to_string(&mut buf).expect("wrong");
    dbg!(read(&buf));
}

fn read(str: &str) -> usize {
    // let mut dic;
    let mut rule: HashMap<usize, Rule> = HashMap::new();
    let mut iter = str.split('\n');
    while let Some(l) = iter.next() {
        if l.is_empty() {
            break;
        }
        if let Some((i, d)) = parse(l) {
            rule.insert(i, d);
        } else {
            panic!("{}", l)
        }
    }
    // dbg!(&rule);
    rule.insert(8, Rule::Or(vec![42], vec![42, 8]));
    rule.insert(11, Rule::Or(vec![42, 31], vec![42, 11, 31]));

    let mut success = 0;
    while let Some(l) = iter.next() {
        if l.is_empty() {
            break;
        }

        let cs = l.chars().collect::<Vec<char>>();
        if check_trace(&rule, &mut vec![0], &cs, 0) {
            success += 1;
        }
        dbg!(&l, success);
    }
    success
}

fn check_trace(
    rule: &HashMap<usize, Rule>,
    stack: &mut Vec<usize>,
    target: &[char],
    from: usize,
) -> bool {
    if let Some(index) = stack.pop() {
        if !stack.is_empty() && target.len() <= from {
            return false;
        }
        if let Some(r) = rule.get(&index) {
            match r {
                Rule::Match(c) => {
                    println!(
                        "try match: {} against {}",
                        index,
                        target[from..].iter().collect::<String>()
                    );
                    if target[from] != *c {
                        return false;
                    }
                    println!("recurse {}", target.len() == from + 1);
                    return check_trace(rule, stack, target, from + 1);
                }
                Rule::Seq(vec) => {
                    println!(
                        "try seq: {} against {}",
                        index,
                        target[from..].iter().collect::<String>()
                    );
                    for i in vec.iter().rev() {
                        stack.push(*i);
                    }
                    return check_trace(rule, stack, target, from);
                }
                Rule::Or(vec1, vec2) => {
                    let mut stack2 = stack.clone();
                    for i in vec1.iter().rev() {
                        stack.push(*i);
                    }
                    let try1 = check_trace(rule, stack, target, from);
                    if try1 {
                        return true;
                    }
                    for i in vec2.iter().rev() {
                        stack2.push(*i);
                    }
                    // println!("backtrack of rule {}: {:?}", index, vec2);
                    return check_trace(rule, &mut stack2, target, from);
                }
            }
        } else {
            panic!(
                "here stack.{}, from.{}, len.{}",
                stack.len(),
                from,
                target.len()
            );
            // return target.len() == from;
        }
    }
    return target.len() == from;
}

#[derive(Debug, PartialEq)]
enum Rule {
    Match(char),
    Or(Vec<usize>, Vec<usize>),
    Seq(Vec<usize>),
}

fn parse(str: &str) -> Option<(usize, Rule)> {
    lazy_static! {
        static ref R0: Regex = Regex::new(r#"^(\d+): "(.)""#).expect("error");
        static ref R1: Regex = Regex::new(r"^(\d+):(( \d+)+)$").expect("error");
        static ref R2: Regex = Regex::new(r"^(\d+):(( \d+)+) \|(( \d+)+)$").expect("error");
    }
    if let Some(m) = R0.captures(str) {
        let i = m[1].parse::<usize>().expect("wrong");
        let c = m[2].parse::<char>().expect("wrong");
        return Some((i, Rule::Match(c)));
    } else if let Some(m) = R1.captures(str) {
        let i = m[1].parse::<usize>().expect("wrong");
        let mut vec: Vec<usize> = Vec::new();
        for n in m[2].split_ascii_whitespace() {
            vec.push(n.parse::<usize>().expect("strange"));
        }
        return Some((i, Rule::Seq(vec)));
    } else if let Some(m) = R2.captures(str) {
        let i = m[1].parse::<usize>().expect("wrong");
        let mut vec1: Vec<usize> = Vec::new();
        for n in m[2].split_ascii_whitespace() {
            vec1.push(n.parse::<usize>().expect("strange"));
        }
        let mut vec2: Vec<usize> = Vec::new();
        for n in m[4].split_ascii_whitespace() {
            vec2.push(n.parse::<usize>().expect("strange"));
        }
        return Some((i, Rule::Or(vec1, vec2)));
    }
    None
}

mod test {
    use super::*;
    const TEST1: &str = "\
0: 4 1 5
1: 2 3 | 3 2
2: 4 4 | 5 5
3: 4 5 | 5 4
4: \"a\"
5: \"b\"

ababbb
bababa
abbbab
aaabbb
aaaabbb";
    #[test]
    fn test1() {
        assert_eq!(read(TEST1), 2);
    }
}
