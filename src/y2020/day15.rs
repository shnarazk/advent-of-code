//! <https://adventofcode.com/2020/day/15>
#![allow(unused_imports)]
use {
    crate::y2020::traits::{Description, ProblemObject, ProblemSolver},
    std::collections::HashMap,
};

pub fn day15(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

#[derive(Debug, PartialEq)]
struct Object {}

impl ProblemObject for Object {
    fn parse(_s: &str) -> Option<Self> {
        None
    }
}

#[derive(Debug, PartialEq)]
struct Setting {
    dic: HashMap<usize, usize>,
    last: usize,
    clock: usize,
}

impl ProblemSolver<String, usize, usize> for Setting {
    const YEAR: usize = 2020;
    const DAY: usize = 15;
    const DELIMITER: &'static str = ",";
    fn default() -> Self {
        Setting {
            dic: HashMap::new(),
            last: 0,
            clock: 0,
        }
    }
    fn insert(&mut self, cs: String) {
        if let Ok(n) = cs.trim().parse::<usize>() {
            self.clock += 1;
            *self.dic.entry(n).or_insert(0) = self.clock;
            self.last = n;
        }
    }
    fn part1(&mut self) -> usize {
        self.run_to(2020)
    }
    fn part2(&mut self) -> usize {
        self.run_to(30000000)
    }
}

impl Setting {
    fn run_to(&mut self, limit: usize) -> usize {
        self.clock += 1;
        loop {
            let last_entry = self.dic.entry(self.last).or_insert(0);
            if *last_entry == 0 {
                *last_entry = self.clock - 1;
                self.last = 0;
            } else {
                self.last = self.clock - 1 - *last_entry;
                *last_entry = self.clock - 1;
            }
            if limit == self.clock {
                return self.last;
            }
            self.clock += 1;
        }
    }
}

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::y2020::traits::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        assert_eq!(
            Setting::parse(Description::TestData("1,3,2".to_string())).run(1),
            Answer::Part1(1)
        );
        assert_eq!(
            Setting::parse(Description::TestData("2,1,3".to_string())).run(1),
            Answer::Part1(10)
        );
        assert_eq!(
            Setting::parse(Description::TestData("1,2,3".to_string())).run(1),
            Answer::Part1(27)
        );
        assert_eq!(
            Setting::parse(Description::TestData("2,3,1".to_string())).run(1),
            Answer::Part1(78)
        );
        assert_eq!(
            Setting::parse(Description::TestData("3,2,1".to_string())).run(1),
            Answer::Part1(438)
        );
        assert_eq!(
            Setting::parse(Description::TestData("3,1,2".to_string())).run(1),
            Answer::Part1(1836)
        );
    }
    #[test]
    fn test_part2() {
        assert_eq!(
            Setting::parse(Description::TestData("0,3,6".to_string())).run(2),
            Answer::Part2(175594)
        );
        assert_eq!(
            Setting::parse(Description::TestData("1,3,2".to_string())).run(2),
            Answer::Part2(2578)
        );
    }
}
