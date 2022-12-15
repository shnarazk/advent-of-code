//! <https://adventofcode.com/2022/day/15>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::collections::HashSet,
};

type Loc = (isize, isize);

struct BorderIterator {
    now: Option<Loc>,
    points: Vec<Loc>,
    vec: Loc,
}

impl Iterator for BorderIterator {
    type Item = Loc;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ref mut p) = self.now {
            if p == self.points.last().unwrap() {
                self.points.pop();
                self.vec = match self.points.len() {
                    4 => (1, 1),
                    3 => (-1, 1),
                    2 => (-1, -1),
                    1 => (1, -1),
                    0 => {
                        self.now = None;
                        return self.now;
                    }
                    _ => unreachable!(),
                };
            }
            p.0 += self.vec.0;
            p.1 += self.vec.1;
        }
        self.now
    }
}

fn out_of_border(sensor: &Loc, nearest: &Loc) -> BorderIterator {
    let range = 1 + (sensor.0.abs_diff(nearest.0) + sensor.1.abs_diff(nearest.1)) as isize;
    BorderIterator {
        now: Some((sensor.0, sensor.1 - range)),
        points: vec![
            (sensor.0, sensor.1 - range),
            (sensor.0 - range, sensor.1),
            (sensor.0, sensor.1 + range),
            (sensor.0 + range, sensor.1),
            (sensor.0, sensor.1 - range),
        ],
        vec: (1, 1),
    }
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(Loc, Loc)>,
}

#[aoc(2022, 15)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser =
            regex!(r"^Sensor at x=(-?\d+), y=(-?\d+): closest beacon is at x=(-?\d+), y=(-?\d+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            (segment[1].parse::<isize>()?, segment[2].parse::<isize>()?),
            (segment[3].parse::<isize>()?, segment[4].parse::<isize>()?),
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let target = 2_000_000; // 10;
        let mut on_target: HashSet<isize> = HashSet::new();
        let mut bands = Vec::new();
        for (i, p) in self.line.iter().enumerate() {
            let range = p.0 .0.abs_diff(p.1 .0) + p.0 .1.abs_diff(p.1 .1);
            if let Some(len) = range.checked_sub(p.0 .1.abs_diff(target)) {
                let range_on_target = (p.0 .0 - len as isize, p.0 .0 + len as isize);
                println!("{i}-th{:?}:range {:?}", p.0, &range_on_target);
                bands.push(range_on_target);
            }
            if p.1 .1 == target {
                on_target.insert(p.1 .0);
            }
        }
        bands.sort();
        let mut total: usize = 0;
        let mut in_range = false;
        let mut start = 0;
        let mut end = 0;
        for b in bands.iter() {
            if in_range {
                if b.0 <= end {
                    end = end.max(b.1);
                } else {
                    total += (end - start + 1) as usize;
                    in_range = false;
                }
            } else {
                in_range = true;
                start = b.0;
                end = b.1;
            }
        }
        if in_range {
            total += (end - start + 1) as usize;
        }
        total - on_target.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        for p in self.line.iter() {
            for o in out_of_border(&p.0, &p.1)
                .filter(|o| 0 <= o.0 && o.0 <= 4000000 && 0 <= o.1 && o.1 <= 4000000)
            {
                if self.line.iter().all(|c| {
                    let range = c.0 .0.abs_diff(c.1 .0) + c.0 .1.abs_diff(c.1 .1);
                    let dist = c.0 .0.abs_diff(o.0) + c.0 .1.abs_diff(o.1);
                    range < dist
                }) {
                    return (o.0 * 4000000 + o.1) as usize;
                }
            }
        }
        unreachable!()
    }
}
