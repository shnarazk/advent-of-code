//! <https://adventofcode.com/2020/day/10>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    vec: Vec<usize>,
}

#[aoc(2020, 10)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        dbg!(&block);
        self.vec.push(block.parse::<usize>()?);
        Ok(())
    }
    fn after_insert(&mut self) {
        self.vec.insert(0, 0);
    }
    fn part1(&mut self) -> usize {
        self.vec.sort_unstable();
        let mut diff1 = 0;
        let mut diff3 = 0;
        for i in 1..self.vec.len() {
            match self.vec[i] - self.vec[i - 1] {
                1 => diff1 += 1,
                3 => diff3 += 1,
                _ => panic!("wrong"),
            }
        }
        diff3 += 1;
        assert_eq!(self.vec.len(), diff1 + diff3);
        diff1 * diff3
    }
    fn part2(&mut self) -> usize {
        self.vec.sort_unstable();
        let mx = *self.vec.last().unwrap();
        let mut count: Vec<usize> = vec![0; mx + 1];
        count[0] = 1;
        for n in &self.vec[1..] {
            count[*n] += count[*n - 1];
            if 2 <= *n {
                count[*n] += count[*n - 2];
            }
            if 3 <= *n {
                count[*n] += count[*n - 3];
            }
        }
        dbg!(&count);
        *count.last().unwrap()
    }
}

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    const TEST1: &str = "\
16
10
15
5
1
11
7
19
6
12
4";

    const TEST2: &str = "\
28
33
18
42
31
14
46
20
48
47
24
23
49
45
19
38
39
11
1
32
25
35
8
17
7
9
4
2
34
10
3";
    #[test]
    fn test_part1_1() {
        assert_eq!(
            Puzzle::solve(Description::TestData(TEST1.to_string()), 1),
            Answer::Part1(7 * 5)
        );
    }

    #[test]
    fn test_part2_1() {
        assert_eq!(
            Puzzle::solve(Description::TestData(TEST1.to_string()), 2),
            Answer::Part2(8)
        );
    }

    #[test]
    fn test_part1_2() {
        assert_eq!(
            Puzzle::solve(Description::TestData(TEST2.to_string()), 1),
            Answer::Part1(22 * 10)
        );
    }
    #[test]
    fn test_part2_2() {
        assert_eq!(
            Puzzle::solve(Description::TestData(TEST2.to_string()), 2),
            Answer::Part2(19208)
        );
    }
}
