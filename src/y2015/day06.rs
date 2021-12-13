use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    lazy_static::lazy_static,
    regex::Regex,
};

#[derive(Debug, PartialEq)]
enum Code {
    Toggle(usize, usize, usize, usize),
    TurnOff(usize, usize, usize, usize),
    TurnOn(usize, usize, usize, usize),
}

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<Code>,
}

#[aoc(2015, 6)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        lazy_static! {
            static ref PARSER: Regex = Regex::new(
                r"^(toggle|turn off|turn on) ([0-9]+),([0-9]+) through ([0-9]+),([0-9]+)$"
            )
            .expect("wrong");
        }
        let segment = PARSER.captures(block).ok_or(ParseError)?;
        let num: Vec<usize> = (2..=5)
            .map(|i| segment[i].parse::<usize>().expect("-"))
            .collect();
        self.line.push(match &segment[1] {
            "toggle" => Code::Toggle(num[0], num[1], num[2], num[3]),
            "turn off" => Code::TurnOff(num[0], num[1], num[2], num[3]),
            "turn on" => Code::TurnOn(num[0], num[1], num[2], num[3]),
            _ => unreachable!(),
        });
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut lights: [[bool; 1000]; 1000] = [[false; 1000]; 1000];
        for c in self.line.iter() {
            match c {
                Code::Toggle(bj, bi, ej, ei) => {
                    for v in &mut lights[*bj..=*ej] {
                        for l in &mut v[*bi..=*ei] {
                            *l = !*l;
                        }
                    }
                }
                Code::TurnOff(bj, bi, ej, ei) => {
                    for v in &mut lights[*bj..=*ej] {
                        for l in &mut v[*bi..=*ei] {
                            *l = false;
                        }
                    }
                }
                Code::TurnOn(bj, bi, ej, ei) => {
                    for v in &mut lights[*bj..=*ej] {
                        for l in &mut v[*bi..=*ei] {
                            *l = true;
                        }
                    }
                }
            }
        }
        lights
            .iter()
            .map(|v| v.iter().filter(|l| **l).count())
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut lights: [[usize; 1000]; 1000] = [[0; 1000]; 1000];
        for c in self.line.iter() {
            match c {
                Code::Toggle(bj, bi, ej, ei) => {
                    for v in &mut lights[*bj..=*ej] {
                        for l in &mut v[*bi..=*ei] {
                            *l += 2;
                        }
                    }
                }
                Code::TurnOff(bj, bi, ej, ei) => {
                    for v in &mut lights[*bj..=*ej] {
                        for l in &mut v[*bi..=*ei] {
                            *l = if *l == 0 { 0 } else { *l - 1 };
                        }
                    }
                }
                Code::TurnOn(bj, bi, ej, ei) => {
                    for v in &mut lights[*bj..=*ej] {
                        for l in &mut v[*bi..=*ei] {
                            *l += 1;
                        }
                    }
                }
            }
        }
        lights.iter().map(|v| v.iter().sum::<usize>()).sum()
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
        const TEST1: &str = "0\n1\n2";
        assert_eq!(
            Puzzle::solve(Description::TestData(TEST1.to_string()), 1),
            Answer::Part1(0)
        );
    }
}
