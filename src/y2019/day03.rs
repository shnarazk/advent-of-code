//! <https://adventofcode.com/2019/day/3>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::{HashMap, HashSet},
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<(isize, isize)>>,
}

mod parser {
    use {
        crate::parser::parse_isize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<(isize, isize)> {
        alt((
            seq!(_: "U", parse_isize).map(|(d,)| (-d, 0)),
            seq!(_: "D", parse_isize).map(|(d,)| (d, 0)),
            seq!(_: "L", parse_isize).map(|(d,)| (0, -d)),
            seq!(_: "R", parse_isize).map(|(d,)| (0, d)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Vec<(isize, isize)>>> {
        separated(
            1..,
            separated(1.., parse_line, ",").map(|v: Vec<(isize, isize)>| v),
            newline,
        )
        .parse_next(s)
    }
}

#[aoc(2019, 3)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut checked: HashSet<(isize, isize)> = HashSet::new();
        let mut oy = 0;
        let mut ox = 0;
        for (dy, dx) in self.line[0].iter() {
            for y in 0.min(*dy)..=0.max(*dy) {
                for x in 0.min(*dx)..=0.max(*dx) {
                    checked.insert((oy + y, ox + x));
                }
            }
            oy += dy;
            ox += dx;
        }
        let mut lowest = usize::MAX / 4;
        oy = 0;
        ox = 0;
        checked.remove(&(0, 0));
        for (dy, dx) in self.line[1].iter() {
            for y in 0.min(*dy)..=0.max(*dy) {
                for x in 0.min(*dx)..=0.max(*dx) {
                    let py = oy + y;
                    let px = ox + x;
                    if checked.contains(&(py, px)) && (py.abs() + px.abs()) < (lowest as isize) {
                        lowest = (py.abs() + px.abs()) as usize;
                    }
                }
            }
            oy += dy;
            ox += dx;
        }
        lowest
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut checked: HashMap<(isize, isize), usize> = HashMap::new();
        let mut oy = 0;
        let mut ox = 0;
        let mut time = 0;
        for (dy, dx) in self.line[0].iter() {
            for y in 0..=dy.abs() {
                for x in 0..=dx.abs() {
                    if y == 0 && x == 0 {
                        continue;
                    }
                    oy += dy.signum();
                    ox += dx.signum();
                    time += 1;
                    checked.insert((oy, ox), time);
                }
            }
        }
        let mut lowest = usize::MAX / 4;
        oy = 0;
        ox = 0;
        time = 0;
        checked.remove(&(0, 0));
        for (dy, dx) in self.line[1].iter() {
            for y in 0..=dy.abs() {
                for x in 0..=dx.abs() {
                    if y == 0 && x == 0 {
                        continue;
                    }
                    oy += dy.signum();
                    ox += dx.signum();
                    time += 1;
                    if let Some(t) = checked.get(&(oy, ox)) {
                        // println!("({}, {}) @ {}", oy, ox, t);
                        if time + t < lowest {
                            lowest = time + t;
                        }
                    }
                }
            }
        }
        lowest
    }
}
