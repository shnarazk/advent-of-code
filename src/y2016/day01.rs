//! <https://adventofcode.com/2016/day/01>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashSet,
};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Turn {
    Right(usize),
    Left(usize),
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Turn>,
}

mod parser {
    use {
        super::*,
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            combinator::{alt, separated},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Turn> {
        alt((
            ('L', parse_usize).map(|(_, n)| Turn::Left(n)),
            ('R', parse_usize).map(|(_, n)| Turn::Right(n)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Turn>> {
        separated(1.., parse_line, ", ").parse_next(s)
    }
}

#[aoc(2016, 1)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut rot: isize = 0;
        let mut x: isize = 0;
        let mut y: isize = 0;
        for inst in self.line.iter() {
            let n: usize;
            match inst {
                Turn::Right(rn) => {
                    rot = (rot + 5) % 4;
                    n = *rn;
                }
                Turn::Left(rn) => {
                    rot = (rot + 3) % 4;
                    n = *rn;
                }
            }
            match rot {
                0 => y += n as isize,
                1 => x += n as isize,
                2 => y -= n as isize,
                3 => x -= n as isize,
                _ => unreachable!(),
            }
        }
        (x.abs() + y.abs()) as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut pos: HashSet<(isize, isize)> = HashSet::new();

        let mut rot: isize = 0;
        let mut x: isize = 0;
        let mut y: isize = 0;
        for inst in self.line.iter() {
            let n: usize;
            match inst {
                Turn::Right(rn) => {
                    rot = (rot + 5) % 4;
                    n = *rn;
                }
                Turn::Left(rn) => {
                    rot = (rot + 3) % 4;
                    n = *rn;
                }
            }
            for _ in 0..n {
                match rot {
                    0 => y += 1,
                    1 => x += 1,
                    2 => y -= 1,
                    3 => x -= 1,
                    _ => unreachable!(),
                }
                if pos.contains(&(x, y)) {
                    return (x.abs() + y.abs()) as usize;
                } else {
                    pos.insert((x, y));
                }
            }
        }
        0
    }
}
