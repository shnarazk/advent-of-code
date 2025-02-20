//! <https://adventofcode.com/2023/day/16>
//! Improvement:
//    Map mirrors to bitmaps of energized positions, then merorize it.
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::{Dim2, GeometricAddition},
    },
    std::collections::HashSet,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
    size: Dim2<isize>,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Beam {
    pos: Dim2<isize>,
    dir: Dim2<isize>,
}

impl Beam {
    fn go_forward(&self, h: usize, w: usize) -> Option<Dim2<isize>> {
        self.pos.move_to(self.dir, h, w).map(|b| *b)
    }
    fn is_vert(&self) -> bool {
        self.dir.1 == 0
    }
}

#[aoc(2023, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn parse_block(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.trim().chars().collect::<Vec<_>>());
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.size = (self.line.len() as isize, self.line[0].len() as isize);
    }
    fn part1(&mut self) -> Self::Output1 {
        self.count(Beam {
            pos: (0, -1),
            dir: (0, 1),
        })
    }
    fn part2(&mut self) -> Self::Output2 {
        let height = self.size.1;
        let width = self.size.1;
        (-1..=height)
            .map(|y| {
                (-1..=width)
                    .map(|x| (y, x))
                    .filter(|(y, x)| {
                        ((*x == -1 || *x == width) && (0 <= *y && *y < height))
                            || ((*y == -1 || *y == height) && (0 <= *x && *x < width))
                    })
                    .map(|(y, x)| {
                        self.count(Beam {
                            pos: (y, x),
                            dir: if y == -1 {
                                (1, 0)
                            } else if y == height {
                                (-1, 0)
                            } else if x == -1 {
                                (0, 1)
                            } else {
                                (0, -1)
                            },
                        })
                    })
                    .max()
                    .unwrap()
            })
            .max()
            .unwrap()
    }
}

impl Puzzle {
    fn count(&mut self, start: Beam) -> usize {
        let height = self.size.0 as usize;
        let width = self.size.1 as usize;
        let mut energized: HashSet<Dim2<isize>> = HashSet::new();
        let mut checked: HashSet<Beam> = HashSet::new();
        let mut to_check: Vec<Beam> = Vec::new();
        to_check.push(start);
        while let Some(mut b) = to_check.pop() {
            if checked.contains(&b) {
                continue;
            }
            checked.insert(b.clone());
            energized.insert(b.pos);
            let Some(pos) = b.go_forward(height, width) else {
                continue;
            };
            b.pos = pos;
            match (self.line[pos.0 as usize][pos.1 as usize], b.is_vert()) {
                ('/', true) | ('/', false) => b.dir = (-b.dir.1, -b.dir.0),
                ('\\', true) | ('\\', false) => b.dir = (b.dir.1, b.dir.0),
                ('|', false) => {
                    to_check.push(Beam { pos, dir: (-1, 0) });
                    b.dir = (1, 0);
                }
                ('-', true) => {
                    to_check.push(Beam { pos, dir: (0, -1) });
                    b.dir = (0, 1);
                }
                _ => (),
            }
            to_check.push(b);
        }
        energized.len() - 1 // the light came from out of the region.
    }
}
