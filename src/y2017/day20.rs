//! <https://adventofcode.com/2017/day/20>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

type Dim3 = (isize, isize, isize);

fn add(a: &Dim3, other: &Dim3) -> Dim3 {
    (a.0 + other.0, a.1 + other.1, a.2 + other.2)
}

fn distance(a: &Dim3) -> usize {
    a.0.unsigned_abs() + a.1.unsigned_abs() + a.2.unsigned_abs()
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Particle {
    position: Dim3,
    velocity: Dim3,
    accelerate: Dim3,
}

impl Particle {
    fn update(&mut self) -> &Self {
        self.velocity = add(&self.velocity, &self.accelerate);
        self.position = add(&self.position, &self.velocity);
        self
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Particle>,
}

mod parser {
    use {
        super::Particle,
        crate::parser::parse_isize,
        winnow::{
            ascii::newline,
            combinator::{separated, seq},
            ModalResult, Parser,
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Particle> {
        seq!(_: "p=<", parse_isize, _: ",", parse_isize, _: ",", parse_isize, _: ">, v=<", parse_isize, _: ",", parse_isize, _: ",", parse_isize, _: ">, a=<", parse_isize, _: ",", parse_isize, _: ",", parse_isize, _: ">")
            .map(|(p1, p2, p3, v1, v2, v3, a1, a2, a3)| Particle {
               position: (p1, p2, p3),
               velocity: (v1, v2, v3),
               accelerate: (a1, a2, a3) }
            )
            .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Particle>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2017, 20)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parser::parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut mi = 0;
        let mut md = usize::MAX;
        for (i, d) in self
            .line
            .iter()
            .map(|p| distance(&p.accelerate))
            .enumerate()
        {
            if d < md {
                md = d;
                mi = i;
            }
        }
        mi
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut count: HashMap<Dim3, usize> = HashMap::new();
        let mut c = self.line.len();
        for _ in 0..10000 {
            for p in self.line.iter_mut() {
                p.update();
                *count.entry(p.position).or_insert(0) += 1;
            }
            let mut tmp = self
                .line
                .iter()
                .filter(|p| count.get(&p.position) == Some(&1))
                .cloned()
                .collect::<Vec<_>>();
            std::mem::swap(&mut self.line, &mut tmp);
            count.clear();
            if self.line.len() < c {
                c = self.line.len();
            }
        }
        c
    }
}
