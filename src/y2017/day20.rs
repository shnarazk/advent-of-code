//! <https://adventofcode.com/2017/day/20>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
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

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Particle>,
}

#[aoc(2017, 20)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // p=<77,625,94>, v=<-13,-62,14>, a=<1,3,-2>
        let parser = regex!(
            r"^p=<(-?\d+),(-?\d+),(-?\d+)>, v=<(-?\d+),(-?\d+),(-?\d+)>, a=<(-?\d+),(-?\d+),(-?\d+)>$"
        );
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push(Particle {
            position: (
                segment[1].parse::<isize>()?,
                segment[2].parse::<isize>()?,
                segment[3].parse::<isize>()?,
            ),
            velocity: (
                segment[4].parse::<isize>()?,
                segment[5].parse::<isize>()?,
                segment[6].parse::<isize>()?,
            ),
            accelerate: (
                segment[7].parse::<isize>()?,
                segment[8].parse::<isize>()?,
                segment[9].parse::<isize>()?,
            ),
        });
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
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
                c = dbg!(self.line.len());
            }
        }
        c
    }
}
