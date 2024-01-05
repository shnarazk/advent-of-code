//! <https://adventofcode.com/2020/day/6>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    dic: Vec<(usize, HashMap<char, usize>)>,
}

#[aoc(2020, 6)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let mut dic: HashMap<char, usize> = HashMap::new();
        let n = block.lines().count();
        for ch in block.chars() {
            if ch.is_ascii_lowercase() {
                *dic.entry(ch).or_insert(0) += 1;
            }
        }
        self.dic.push((n, dic));
        Ok(())
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

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
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
            Puzzle::solve(Description::TestData(TEST1.to_string()), 1),
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
            Puzzle::solve(Description::TestData(TEST2.to_string()), 2),
            Answer::Part2(6)
        );
    }
}
