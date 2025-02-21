//! <https://adventofcode.com/2023/day/6>
use crate::{
    framework::{AdventOfCode, ParseError, aoc},
    parser,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
    setting1: Vec<(usize, usize)>,
    setting2: (usize, usize),
}

#[aoc(2023, 6)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = input
            .lines()
            .map(|l| {
                let s = l.split(':').nth(1).unwrap().trim();
                parser::to_usizes(s, &[' ']).unwrap()
            })
            .collect();
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for (i, t) in self.line[0].iter().enumerate() {
            self.setting1.push((*t, self.line[1][i]));
        }
        let s2 = self
            .line
            .iter()
            .map(|vec| {
                let mut s = 0;
                for x in vec.iter() {
                    s = s * 10_usize.pow(x.ilog(10) + 1) + *x;
                }
                s
            })
            .collect::<Vec<_>>();
        self.setting2 = (s2[0], s2[1]);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.setting1
            .iter()
            .map(|(t, d)| (1..*t - 1).filter(|x| *x * (*t - *x) > *d).count())
            .product::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        let (t, d) = self.setting2;
        let a = seek(t, d, (0, t / 2), 1);
        let b = seek(t, d, (a.1, t), -1);
        b.0 - a.1 + 1
    }
}

fn seek(a: usize, b: usize, mut range: (usize, usize), d: isize) -> (usize, usize) {
    while range.1 - range.0 > 1 {
        let mid = (range.0 + range.1) / 2;
        if (mid * (a - mid)) as isize * d < b as isize * d {
            range.0 = mid;
        } else {
            range.1 = mid;
        }
    }
    range
}
