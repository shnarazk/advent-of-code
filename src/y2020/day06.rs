use crate::y2020::traits::{Description, ProblemSolver};
use std::collections::HashMap;

pub fn day06(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

#[derive(Debug, PartialEq)]
struct Setting {
    dic: Vec<(usize, HashMap<char, usize>)>,
}

impl ProblemSolver<String, usize, usize> for Setting {
    const YEAR: usize = 2020;
    const DAY: usize = 6;
    const DELIMITER: &'static str = "\n\n";
    fn default() -> Self {
        Setting { dic: Vec::new() }
    }
    fn insert(&mut self, line: String) {
        let mut dic: HashMap<char, usize> = HashMap::new();
        let n = line.lines().count();
        for ch in line.chars() {
            if ('a'..='z').contains(&ch) {
                *dic.entry(ch).or_insert(0) += 1;
            }
        }
        self.dic.push((n, dic));
    }
    fn part1(&mut self) -> usize {
        self.dic.iter().map(|(_, h)| h.len()).sum()
    }
    fn part2(&mut self) -> usize {
        self.dic
            .iter()
            .map(|(n, h)| h.values().filter(|m| n == *m).count())
            .sum()
    }
}

#[cfg(test)]
mod test {
    use {
        super::*,
        crate::y2020::traits::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        const TEST1: &str = "\
abc

a
b
c

ab
ac

a
a
a
a

b";
        assert_eq!(
            Setting::parse(Description::TestData(TEST1.to_string())).run(1),
            Answer::Part1(11)
        );
    }
    #[test]
    fn test_part2() {
        const TEST2: &str = "\
abc

a
b
c

ab
ac

a
a
a
a

b";
        assert_eq!(
            Setting::parse(Description::TestData(TEST2.to_string())).run(2),
            Answer::Part2(6)
        );
    }
}
