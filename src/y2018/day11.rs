//! <https://adventofcode.com/2018/day/11>
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::Dim2,
    },
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    grid_serial_number: usize,
    map: HashMap<Dim2<usize>, isize>,
}

#[aoc_at(2018, 11)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = String;
    const DELIMITER: &'static str = "\n";
    fn parse_block(&mut self, block: &str) -> Result<(), ParseError> {
        self.grid_serial_number = block.parse::<usize>()?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let map = self.build_value_power_level_map();
        let mut loc: Dim2<usize> = (1, 1);
        let mut point_max: isize = 0;
        for y in 1..=300 - 2 {
            for x in 1..=300 - 2 {
                let mut sum = 0;
                for yy in y..y + 3 {
                    for xx in x..x + 3 {
                        // sum += self.get((xx, yy));
                        sum += map[yy - 1][xx - 1];
                        if point_max < sum {
                            point_max = sum;
                            loc = (x, y);
                        }
                    }
                }
            }
        }
        format!("{},{}", loc.0, loc.1)
    }
    fn part2(&mut self) -> Self::Output2 {
        let map = self.build_value_power_level_map();
        let mut loc = (1, 1, 1);
        let mut point_max: isize = 0;
        for y in 1..=300 {
            for x in 1..=300 {
                let max_square = (301 - y).min(301 - x);
                let mut sum = 0;
                for size in 1..=max_square {
                    for yy in y..y + size {
                        sum += map[yy - 1][x + size - 2]; // ((x + size - 1, yy));
                    }
                    for xx in x..x + size - 1 {
                        sum += map[y + size - 2][xx - 1]; //self.get((xx, y + size - 1));
                    }
                    if point_max < sum {
                        point_max = sum;
                        loc = (x, y, size);
                    }
                }
            }
        }
        format!("{},{},{}", loc.0, loc.1, loc.2)
    }
}

impl Puzzle {
    fn build_value_power_level_map(&self) -> Vec<Vec<isize>> {
        (1..=300)
            .map(|y| {
                (1..=300)
                    .map(|x| {
                        let rack_id = x as isize + 10;
                        let mut power_level = rack_id * (y as isize);
                        power_level += self.grid_serial_number as isize;
                        power_level *= rack_id;
                        power_level /= 100;
                        power_level %= 10;
                        power_level -= 5;
                        power_level
                    })
                    .collect::<Vec<isize>>()
            })
            .collect::<Vec<_>>()
    }
}
