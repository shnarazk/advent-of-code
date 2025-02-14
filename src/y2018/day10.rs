//! <https://adventofcode.com/2018/day/10>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<isize>>,
}

mod parser {
    use {
        crate::parser::parse_isize,
        winnow::{
            ascii::{newline, space0},
            combinator::{separated, seq},
            ModalResult, Parser,
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Vec<isize>> {
        seq!(_: "position=<", _: space0, parse_isize,
            _: ",", _: space0, parse_isize,
            _: "> velocity=<", _: space0, parse_isize,
            _: ",", _: space0, parse_isize,
            _: ">"
        )
        .map(|(a, b, c, d)| vec![a, b, c, d])
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Vec<isize>>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2018, 10)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parser::parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut last: (usize, Vec<Vec<isize>>) = (usize::MAX, Vec::new());
        let mut data = self.line.clone();
        loop {
            let d = self.update(&mut data);
            if last.0 < d.0 {
                self.print(&last.1);
                return 0;
            }
            last = d;
        }
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut last: (usize, Vec<Vec<isize>>) = (usize::MAX, Vec::new());
        let mut data = self.line.clone();
        for step in 0.. {
            let d = self.update(&mut data);
            if last.0 < d.0 {
                return step;
            }
            last = d;
        }
        unreachable!()
    }
}

impl Puzzle {
    fn size(&self, line: &[Vec<isize>]) -> usize {
        let mut y_min: isize = isize::MAX;
        let mut x_min: isize = isize::MAX;
        let mut y_max: isize = isize::MIN;
        let mut x_max: isize = isize::MIN;
        for l in line.iter() {
            x_min = x_min.min(l[0]);
            y_min = y_min.min(l[1]);
            x_max = x_max.max(l[0]);
            y_max = y_max.max(l[1]);
        }
        ((y_max - y_min) * (x_max - x_min)) as usize
    }
    fn print(&self, source: &[Vec<isize>]) {
        let mut map: HashMap<isize, Vec<isize>> = HashMap::new();
        let mut y_min: isize = isize::MAX;
        let mut x_min: isize = isize::MAX;
        let mut y_max: isize = isize::MIN;
        let mut x_max: isize = isize::MIN;
        for l in source.iter() {
            map.entry(l[1]).or_default().push(l[0]);
            x_min = x_min.min(l[0]);
            y_min = y_min.min(l[1]);
            x_max = x_max.max(l[0]);
            y_max = y_max.max(l[1]);
        }
        for y in y_min..=y_max {
            if let Some(p) = map.get(&y) {
                for x in x_min..=x_max {
                    print!("{}", if p.contains(&x) { '#' } else { '.' });
                }
            } else {
                for _ in x_min..=x_max {
                    print!(".");
                }
            }
            println!();
        }
    }
    fn update(&mut self, image: &mut [Vec<isize>]) -> (usize, Vec<Vec<isize>>) {
        for l in image.iter_mut() {
            l[0] += l[2];
            l[1] += l[3];
        }
        (self.size(image), image.to_vec())
    }
}
