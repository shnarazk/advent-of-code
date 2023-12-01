//! <https://adventofcode.com/2022/day/15>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::Dim2,
        regex,
    },
    std::collections::HashSet,
};

type Loc = Dim2<isize>;

fn mdist(base: &Loc, target: &Loc) -> usize {
    base.0.abs_diff(target.0) + base.1.abs_diff(target.1)
}

fn cross_at((mut a, mut b): (Loc, Loc), (mut s, mut t): (Loc, Loc)) -> Option<Loc> {
    if b.0 < a.0 {
        std::mem::swap(&mut a, &mut b);
    }
    if t.0 < s.0 {
        std::mem::swap(&mut s, &mut t);
    }
    let f = (b.1 - a.1).signum();
    let g = (t.1 - s.1).signum();
    if f == g {
        return None;
    }
    let x = ((s.1 + f * a.0) - (a.1 + g * s.0)) / (f - g);
    let y = a.1 + x - a.0;
    ((a.0 <= x) && (x <= b.0) && (a.1 <= y) && (y <= b.1)).then_some((x, y))
}

fn intersections(a: &Loc, ab: &Loc, b: &Loc, bb: &Loc) -> Vec<Loc> {
    let d0 = mdist(a, ab) as isize + 1;
    let d1 = mdist(b, bb) as isize + 1;
    [
        cross_at(
            ((a.0, a.1 - d0), (a.0 + d0, a.1)),
            ((b.0 - d1, b.1), (b.0, b.1 - d1)),
        ),
        cross_at(
            ((a.0, a.1 - d0), (a.0 + d0, a.1)),
            ((b.0 + d1, b.1), (b.0, b.1 + d1)),
        ),
        cross_at(
            ((a.0, a.1 + d0), (a.0 - d0, a.1)),
            ((b.0 - d1, b.1), (b.0, b.1 - d1)),
        ),
        cross_at(
            ((a.0, a.1 + d0), (a.0 - d0, a.1)),
            ((b.0 + d1, b.1), (b.0, b.1 + d1)),
        ),
        cross_at(
            ((a.0, a.1 + d0), (a.0 + d0, a.1)),
            ((b.0 - d1, b.1), (b.0, b.1 + d1)),
        ),
        cross_at(
            ((a.0, a.1 + d0), (a.0 + d0, a.1)),
            ((b.0 + d1, b.1), (b.0, b.1 - d1)),
        ),
        cross_at(
            ((a.0, a.1 - d0), (a.0 - d0, a.1)),
            ((b.0 - d1, b.1), (b.0, b.1 + d1)),
        ),
        cross_at(
            ((a.0, a.1 - d0), (a.0 - d0, a.1)),
            ((b.0 + d1, b.1), (b.0, b.1 - d1)),
        ),
    ]
    .iter()
    .filter_map(|s| *s)
    .collect::<Vec<_>>()
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
    fn end_of_data(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let target = 2_000_000; // 10;
        let mut on_target: HashSet<isize> = HashSet::new();
        let mut bands = Vec::new();
        for (i, p) in self.line.iter().enumerate() {
            if let Some(len) = mdist(&p.0, &p.1).checked_sub(p.0 .1.abs_diff(target)) {
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
        const BOUNDARY: isize = 4000000; // 20
        for (sensor, beacon) in self.line.iter() {
            let r = mdist(sensor, beacon);
            let overlapped = self
                .line
                .iter()
                .filter(|(s, b)| mdist(sensor, s) <= 1 + r + mdist(s, b))
                .map(|(s, b)| (*s, *b))
                .collect::<Vec<(Loc, Loc)>>();
            for (s, b) in overlapped.iter() {
                for o in intersections(sensor, beacon, s, b)
                    .iter()
                    .filter(|o| 0 <= o.0 && o.0 <= BOUNDARY && 0 <= o.1 && o.1 <= BOUNDARY)
                {
                    if overlapped.iter().all(|(s, b)| mdist(s, b) < mdist(s, o)) {
                        return (o.0 * 4000000 + o.1) as usize;
                    }
                }
            }
        }
        unreachable!()
    }
}
