#![allow(unused_imports)]
#![allow(dead_code)]
use crate::{Description, ProblemObject, ProblemSolver};
use {lazy_static::lazy_static, regex::Regex, std::collections::HashMap};

pub fn go(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

// #[derive(Debug, PartialEq)]
type Object = usize;

// impl ProblemObject for Object {
//     fn parse(s: &str) -> Option<Self> {
//         if let Ok(x) = s.parse::<usize>() {
//             Some(x)
//         } else {
//             None
//         }
//     }
// }

#[derive(Debug, PartialEq)]
struct Setting {
    line: Vec<usize>
}

impl ProblemSolver<Object, usize, usize> for Setting {
    const YEAR: usize = 2021;
    const DAY: usize = 1;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Setting {
         line: Vec::new()
        }
    }
    fn insert(&mut self, object: Object) {
        self.line.push(object);
    }
    fn part1(&mut self) -> usize {
        let mut last = self.line[0];
        let mut count = 0;
        for l in self.line.iter() {
            if last < *l {
                count += 1;
            }
            last = *l;
        }
        count
    }
    fn part2(&mut self) -> usize {
        fn average3(vec: &[usize]) -> usize {
            assert!(2 < vec.len());
            vec[0] + vec[1] + vec[2]
        }
        let mut last = average3(&self.line);
        let mut count = 0;
        for i in 0..self.line.len() - 2 {
            let new = average3(&self.line[i..]);
            if last < new {
                count += 1;
            }
            last = new;
        }
        count
    }
}

fn check_line1(str: &str) -> usize {
    lazy_static! {
        static ref PARSER: Regex =
            Regex::new(r"^([0-9]+)-([0-9]+) ([a-zA-Z]): (.*)$").expect("wrong regex");
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

#[cfg(test)]
mod test {
    use {
        super::*,
        crate::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        const TEST1: &str = "0\n1\n2";
        assert_eq!(
            Setting::parse(Description::TestData(TEST1.to_string())).run(1),
            Answer::Part1(0)
        );
    }
    #[test]
    fn test_part2() {
        const TEST2: &str = "0\n1\n2";
        assert_eq!(
            Setting::parse(Description::TestData(TEST2.to_string())).run(2),
            Answer::Part2(0)
        );
    }
}
