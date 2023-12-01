//! <https://adventofcode.com/2018/day/11>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

type Dim2 = (usize, usize);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: usize,
    map: HashMap<Dim2, isize>,
}

#[aoc(2018, 11)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, _block: &str) -> Result<(), ParseError> {
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.line = 3463;
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut loc: Dim2 = (1, 1);
        let mut point_max: isize = 0;
        for y in 1..=300 - 2 {
            for x in 1..=300 - 2 {
                let mut sum = 0;
                for yy in y..y + 3 {
                    for xx in x..x + 3 {
                        sum += self.get((xx, yy));
                        if point_max < sum {
                            point_max = sum;
                            loc = (x, y);
                        }
                    }
                }
            }
        }
        dbg!(loc);
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut loc = (1, 1, 1);
        let mut point_max: isize = 0;
        for y in 1..=300 {
            for x in 1..=300 {
                let max_square = (301 - y).min(301 - x);
                let mut sum = 0;
                for size in 1..=max_square {
                    for yy in y..y + size {
                        sum += self.get((x + size - 1, yy));
                    }
                    for xx in x..x + size - 1 {
                        sum += self.get((xx, y + size - 1));
                    }
                    if point_max < sum {
                        point_max = sum;
                        loc = (x, y, size);
                    }
                }
            }
        }
        dbg!(loc);
        0
    }
}

impl Puzzle {
    fn get(&mut self, at: Dim2) -> isize {
        if let Some(p) = self.map.get(&at) {
            return *p;
        }
        let rack_id = at.0 as isize + 10;
        let mut power_level = rack_id * at.1 as isize;
        power_level += self.line as isize;
        power_level *= rack_id;
        power_level /= 100;
        power_level %= 10;
        power_level -= 5;
        self.map.insert(at, power_level);
        power_level
    }
}

#[test]
fn y2018day11part1_test1() {
    let mut p = Puzzle {
        line: 8,
        ..Puzzle::default()
    };
    assert_eq!(p.get((3, 5)), 4);
    p.line = 57;
    assert_eq!(p.get((122, 79)), -5);
}
