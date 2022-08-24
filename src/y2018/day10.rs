//! <https://adventofcode.com/2018/day/10>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<isize>>,
}

#[aoc(2018, 10)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // position=< 50781, -20123> velocity=<-5,  2>
        let parser = regex!(r"^position=< *(-?\d+), +(-?\d+)> velocity=< *(-?\d+), +(-?\d+)>");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push(vec![
            segment[1].parse::<_>()?,
            segment[2].parse::<_>()?,
            segment[3].parse::<_>()?,
            segment[4].parse::<_>()?,
        ]);
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut buffer = String::new();
        let stdin = std::io::stdin();
        loop {
            let too_big = self.print();
            if !too_big {
                buffer.clear();
                stdin.read_line(&mut buffer).expect("strange error");
                if buffer.starts_with('c') {
                    return 1;
                }
            }
            self.update();
        }
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut buffer = String::new();
        let stdin = std::io::stdin();
        for step in 0.. {
            let too_big = self.print();
            if !too_big {
                buffer.clear();
                stdin.read_line(&mut buffer).expect("strange error");
                if buffer.starts_with('c') {
                    return step;
                }
            }
            self.update();
        }
        unreachable!();
    }
}

impl Puzzle {
    fn print(&self) -> bool {
        let mut map: HashMap<isize, Vec<isize>> = HashMap::new();
        let mut y_min: isize = isize::MAX;
        let mut x_min: isize = isize::MAX;
        let mut y_max: isize = isize::MIN;
        let mut x_max: isize = isize::MIN;
        for l in self.line.iter() {
            map.entry(l[1]).or_insert(Vec::new()).push(l[0]);
            x_min = x_min.min(l[0]);
            y_min = y_min.min(l[1]);
            x_max = x_max.max(l[0]);
            y_max = y_max.max(l[1]);
        }
        if 100 < y_max - y_min || 100 < x_max - x_min {
            // dbg!(y_max - y_min, x_max - x_min);
            return true;
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
        false
    }
    fn update(&mut self) {
        for l in self.line.iter_mut() {
            l[0] += l[2];
            l[1] += l[3];
        }
        // todo!();
    }
}
