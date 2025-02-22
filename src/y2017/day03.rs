//! <https://adventofcode.com/2017/day/3>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<usize>,
}

#[aoc(2017, 3)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            self.line.push(l.trim().parse::<usize>()?);
        }
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut distance = 0;
        'next: for n in self.line.iter() {
            for radius in 0_usize.. {
                let max_node = (2 * radius + 1).pow(2);
                if *n <= max_node {
                    if 0 < radius {
                        // let start = (2 * (radius - 1) + 1).pow(2) + 1;
                        let mut corner: usize = max_node;
                        for _ in 0..4 {
                            corner -= 2 * radius;
                            if corner <= *n {
                                let base = corner + radius;
                                distance = radius + n.abs_diff(base);
                                // dbg!(n, radius, start, max_node, corner, base, distance);
                                // println!();
                                continue 'next;
                            }
                        }
                    }
                    break;
                }
            }
        }
        distance
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut map: HashMap<(isize, isize), usize> = HashMap::new();
        let mut x: isize = 0;
        let mut y: isize = 0;
        macro_rules! insert {
            () => {{
                map.insert(
                    (y, x),
                    *map.get(&(y - 1, x)).unwrap_or(&0)
                        + *map.get(&(y - 1, x + 1)).unwrap_or(&0)
                        + *map.get(&(y, x + 1)).unwrap_or(&0)
                        + *map.get(&(y + 1, x + 1)).unwrap_or(&0)
                        + *map.get(&(y + 1, x)).unwrap_or(&0)
                        + *map.get(&(y + 1, x - 1)).unwrap_or(&0)
                        + *map.get(&(y, x - 1)).unwrap_or(&0)
                        + *map.get(&(y - 1, x - 1)).unwrap_or(&0),
                );
                // dbg!(map.get(&(y, x)).unwrap());
                let value = *map.get(&(y, x)).unwrap();
                if self.line[0] <= value {
                    // println!(" * ({y}, {x}) => {value}");
                    self.line.remove(0);
                    if self.line.is_empty() {
                        return *map.get(&(y, x)).unwrap();
                    }
                }
            }};
        }
        map.insert((y, x), 1);
        for radius in 0.. {
            for i in 0..4 {
                for j in 0..radius * 2 {
                    match i {
                        0 => y -= 1,
                        1 => x -= 1,
                        2 => y += 1,
                        3 => x += 1,
                        _ => unreachable!(),
                    }
                    insert!();
                    if i == 0 && j == radius * 2 - 2 {
                        break;
                    }
                }
            }
            x += 1;
            insert!();
        }
        0
    }
}
