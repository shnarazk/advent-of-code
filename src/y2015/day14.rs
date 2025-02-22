//! <https://adventofcode.com/2015/day/14>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(String, usize, usize, usize)>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline},
            combinator::{separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<(String, usize, usize, usize)> {
        seq!(alpha1, _: " can fly ", parse_usize, _: " km/s for ", parse_usize,
            _: " seconds, but then must rest for ", parse_usize, _: " seconds.")
        .map(|(n, a, b, c)| (n.to_string(), a, b, c))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<(String, usize, usize, usize)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2015, 14)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let t = 2503;
        let mut longest: usize = 0;
        for (_name, speed, duration, rest) in self.line.iter() {
            let n_cycle = t / (duration + rest);
            let extra = (t % (duration + rest)).min(*duration);
            let length = speed * (n_cycle * duration + extra);
            longest = longest.max(length);
            // println!(
            //     "{} flies {} * ({} * {} + {}) = {} km.",
            //     name, speed, n_cycle, duration, extra, length
            // );
        }
        longest
    }
    fn part2(&mut self) -> Self::Output2 {
        let end = 2503;
        let mut point: Vec<usize> = vec![0; self.line.len()];
        let mut dist = point.clone();

        for t in 0..end {
            for (i, (_, speed, duration, rest)) in self.line.iter().enumerate() {
                if (t % (duration + rest)) < *duration {
                    dist[i] += speed;
                }
            }
            // println!("{:?}", dist);
            let longest = dist.iter().max().unwrap();
            for (i, d) in dist.iter().enumerate() {
                if d == longest {
                    point[i] += 1;
                }
            }
        }
        // println!("{} flies {} * ({} * {} + {}) = {} km.", name, speed, n_cycle, duration, extra, length);
        // dbg!(&point);
        point.iter().copied().max().unwrap()
    }
}
