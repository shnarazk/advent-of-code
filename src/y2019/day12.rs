//! <https://adventofcode.com/2019/day/12>
use crate::{
    framework::{AdventOfCode, ParseError, aoc},
    math::lcm,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<[isize; 6]>,
}

mod parser {
    use {
        crate::parser::parse_isize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<[isize; 6]> {
        seq!( _: "<x=", parse_isize, _: ", y=", parse_isize, _: ", z=", parse_isize, _: ">")
            .map(|(a, b, c)| [a, b, c, 0, 0, 0])
            .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<[isize; 6]>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2019, 12)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut delta = Vec::new();
        for _ in self.line.iter() {
            delta.push([0; 3]);
        }
        for _ in 0..1000 {
            // calculate gravities
            for i in 0..self.line.len() {
                for j in i + 1..self.line.len() {
                    for axis in 0..3 {
                        let d = (self.line[j][axis] - self.line[i][axis]).signum();
                        delta[i][axis] += d;
                        delta[j][axis] -= d;
                    }
                }
            }
            // update the velocities by applying gravity
            for (i, moon) in self.line.iter_mut().enumerate() {
                for (axis, m) in moon.iter_mut().skip(3).enumerate() {
                    *m += delta[i][axis];
                    delta[i][axis] = 0;
                }
            }
            // update the positions
            for moon in self.line.iter_mut() {
                for axis in 0..3 {
                    moon[axis] += moon[axis + 3];
                }
            }
        }
        // calculate energy
        let mut total: usize = 0;
        for moon in self.line.iter() {
            let mut potential: usize = 0;
            let mut kinetic: usize = 0;
            for axis in 0..3 {
                potential += moon[axis].unsigned_abs();
                kinetic += moon[axis + 3].unsigned_abs();
            }
            total += potential * kinetic;
        }
        total
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut factor: [usize; 3] = [0, 0, 0];
        let mut delta = Vec::new();
        for _ in self.line.iter() {
            delta.push([0; 3]);
        }
        let start = self.line.clone();
        for time in 1.. {
            // calculate gravities
            for i in 0..self.line.len() {
                for j in i + 1..self.line.len() {
                    for axis in 0..3 {
                        let d = (self.line[j][axis] - self.line[i][axis]).signum();
                        delta[i][axis] += d;
                        delta[j][axis] -= d;
                    }
                }
            }
            // update the velocities by applying gravity
            for (i, moon) in self.line.iter_mut().enumerate() {
                for (axis, m) in moon.iter_mut().skip(3).enumerate() {
                    *m += delta[i][axis];
                    delta[i][axis] = 0;
                }
            }
            // update the positions
            for moon in self.line.iter_mut() {
                for axis in 0..3 {
                    moon[axis] += moon[axis + 3];
                }
            }
            // if self.line.iter().all(|m| m.iter().skip(3).all(|v| *v == 0)) {
            //     return time;
            // }
            if self.line.iter().all(|m| m[3] == 0) && factor[0] == 0 {
                factor[0] = time;
                // dbg!("X", time);
            }
            if self.line.iter().all(|m| m[4] == 0) && factor[1] == 0 {
                factor[1] = time;
                // dbg!("Y", time);
            }
            if self.line.iter().all(|m| m[5] == 0) && factor[2] == 0 {
                factor[2] = time;
                // dbg!("Z", time);
            }
            if factor.iter().all(|a| 0 != *a) {
                // dbg!(&factor);
                let least = lcm(factor[2], lcm(factor[1], factor[0]));
                return least * 2; // least wasn't a solution. So try doubled one.
            }
            if self.line == start {
                return time;
            }
        }
        0
    }
}
