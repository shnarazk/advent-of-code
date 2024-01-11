//! <https://adventofcode.com/2015/day/14>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    regex,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(String, usize, usize, usize)>,
}

#[aoc(2015, 14)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(
            r"^([A-Za-z]+) can fly ([0-9]+) km/s for ([0-9]+) seconds, but then must rest for ([0-9]+) seconds\.$"
        );
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1].to_string(),
            segment[2].parse::<usize>()?,
            segment[3].parse::<usize>()?,
            segment[4].parse::<usize>()?,
        ));
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
