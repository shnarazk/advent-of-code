//! <https://adventofcode.com/2015/day/5>
use crate::framework::{aoc, AdventOfCode, ParseError};

fn is_nice(s: &str) -> bool {
    3 <= s
        .chars()
        .filter(|c| ['a', 'e', 'i', 'o', 'u'].contains(c))
        .count()
        && 1 <= {
            let v: Vec<char> = s.chars().collect::<Vec<char>>();
            v.iter()
                .enumerate()
                .filter(|(i, c)| Some(*c) == v.get(*i + 1))
                .count()
        }
        && !s.contains("ab")
        && !s.contains("cd")
        && !s.contains("pq")
        && !s.contains("xy")
}

fn is_nicer(s: &str) -> bool {
    let v: Vec<char> = s.chars().collect::<Vec<char>>();
    // dbg!(s);
    let mut found = false;
    for i in 2..v.len() - 1 {
        let b2 = v[i - 2];
        let b1 = v[i - 1];
        // println!("{}{}|{:?}", b1, b2, &v[i..]);
        for j in i..v.len() - 1 {
            // println!(" - {:?}", &v[j..]);
            if b2 == v[j] && b1 == v[j + 1] {
                found = true;
                break;
            }
        }
    }
    if !found {
        return false;
    }
    for i in 0..v.len() - 2 {
        // println!("{:?}", &v[i + 2..]);
        if v[i] == v[i + 2] {
            return true;
        }
    }
    false
}

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<String>,
}

#[aoc(2015, 5)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.to_string());
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line.iter().filter(|s| is_nice(s)).count()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line.iter().filter(|s| is_nicer(s)).count()
    }
}

#[cfg(feature = "y2015")]
#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_part1() {
        assert!(is_nice("ugknbfddgicrmopn"));
    }
    #[test]
    fn test_part2() {
        assert!(is_nicer("qjhvhtzxzqqjkmpb"));
        assert!(is_nicer("xxyxx"));
        assert!(!is_nicer("uurcxstgmygtbstg"));
        assert!(!is_nicer("ieodomkazucvgmuy"));
    }
}
