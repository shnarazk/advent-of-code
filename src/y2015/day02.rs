//! <https://adventofcode.com/2015/day/2>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    lazy_static::lazy_static,
    regex::Regex,
};

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    line: Vec<(usize, usize, usize)>,
}

#[aoc(2015, 2)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        lazy_static! {
            static ref PARSER: Regex = Regex::new(r"^([0-9]+)x([0-9]+)x([0-9]+)$").expect("wrong");
        }
        let segment = PARSER.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1].parse::<usize>()?,
            segment[2].parse::<usize>()?,
            segment[3].parse::<usize>()?,
        ));
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut total = 0;
        for (l, w, h) in self.line.iter() {
            total += 2 * (l * w) + 2 * (w * h) + 2 * (h * l) + (l * w).min(w * h).min(h * l);
        }
        total
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut total = 0;
        for (l, w, h) in self.line.iter() {
            let mut v = [l, w, h];
            v.sort_unstable();
            total += 2 * (v[0] + v[1]) + l * w * h;
        }
        total
    }
}

#[cfg(feature = "y2015")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        const TEST1: &str = "2x3x4";
        assert_eq!(
            Puzzle::solve(Description::TestData(TEST1.to_string()), 1),
            Answer::Part1(58)
        );
    }
    #[test]
    fn test_part2() {
        assert_eq!(
            Puzzle::solve(Description::TestData("2x3x4".to_string()), 2),
            Answer::Part2(34)
        );
        assert_eq!(
            Puzzle::solve(Description::TestData("1x1x10".to_string()), 2),
            Answer::Part2(14)
        );
    }
}
