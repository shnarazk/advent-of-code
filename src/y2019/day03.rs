//! <https://adventofcode.com/2019/day/3>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::collections::{HashMap, HashSet},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<(isize, isize)>>,
}

#[aoc(2019, 3)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // dbg!(&block);
        let parser = regex!(r"^([URDL])(\d+)");
        let mut vec = Vec::new();
        for segment in block.split(',') {
            if let Some(seg) = parser.captures(segment) {
                match (&seg[1], seg[2].parse::<isize>()) {
                    ("U", Ok(d)) => vec.push((-d, 0)),
                    ("D", Ok(d)) => vec.push((d, 0)),
                    ("L", Ok(d)) => vec.push((0, -d)),
                    ("R", Ok(d)) => vec.push((0, d)),
                    _ => panic!(),
                }
            }
        }
        self.line.push(vec);
        Ok(())
    }
    fn wrap_up(&mut self) {
        // dbg!(&self.line);
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
        dbg!(checked.len());
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
        dbg!(lowest)
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
        dbg!(checked.len());
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
                        println!("({}, {}) @ {}", oy, ox, t);
                        if time + t < lowest {
                            lowest = time + t;
                        }
                    }
                }
            }
        }
        dbg!(lowest)
    }
}
