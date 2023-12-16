//! <https://adventofcode.com/2023/day/16>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::Dim2,
    },
    std::collections::HashSet,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<char>>,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Beam {
    pos: Dim2<isize>,
    dir: Dim2<isize>,
}

impl Beam {
    fn go_forward(&self, h: usize, w: usize) -> Option<Dim2<isize>> {
        move_to(self.pos, self.dir, h, w)
    }
    fn is_vert(&self) -> bool {
        self.dir.0.abs() == 1 && self.dir.1 == 0
    }
}

#[aoc(2023, 16)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(block.trim().chars().collect::<Vec<_>>());
        Ok(())
    }
    fn end_of_data(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let start = Beam {
            pos: (0, -1),
            dir: (0, 1), // (0, _) has a mirror!
        };
        self.count(start)
    }
    fn part2(&mut self) -> Self::Output2 {
        let height = self.line.len() as isize;
        let width = self.line[0].len() as isize;
        (-1..=height)
            .map(|y| {
                (-1..=width)
                    .map(|x| (y, x))
                    .filter(|(y, x)| {
                        ((*x == -1 || *x == width) && (0 <= *y && *y < height))
                            || ((*y == -1 || *y == height) && (0 <= *x && *x < width))
                    })
                    .map(|(y, x)| {
                        let start = Beam {
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
                        };
                        self.count(start)
                        // 0
                    })
                    .max()
                    .unwrap()
            })
            .max()
            .unwrap()
    }
}

fn move_to(p: Dim2<isize>, d: Dim2<isize>, h: usize, w: usize) -> Option<Dim2<isize>> {
    let y = p.0 + d.0;
    let x = p.1 + d.1;
    (0 <= y && y < h as isize && 0 <= x && x < w as isize).then(|| (y, x))
}

impl Puzzle {
    fn count(&mut self, start: Beam) -> usize {
        let height = self.line.len();
        let width = self.line[0].len();
        let mut energized: HashSet<Dim2<isize>> = HashSet::new();
        let mut checked: HashSet<Beam> = HashSet::new();
        energized.insert(start.pos);
        let mut to_check: Vec<Beam> = Vec::new();
        to_check.push(start);
        while let Some(b) = to_check.pop() {
            if checked.contains(&b) {
                continue;
            }
            checked.insert(b.clone());
            energized.insert(b.pos);
            let Some(pos) = b.go_forward(height, width) else {
                continue;
            };
            match self.line[pos.0 as usize][pos.1 as usize] {
                '/' if b.is_vert() => to_check.push(Beam {
                    pos,
                    dir: (0, -b.dir.0),
                }),
                '/' => to_check.push(Beam {
                    pos,
                    dir: (-b.dir.1, 0),
                }),
                '\\' if b.is_vert() => to_check.push(Beam {
                    pos,
                    dir: (0, b.dir.0),
                }),
                '\\' => to_check.push(Beam {
                    pos,
                    dir: (b.dir.1, 0),
                }),
                '|' if !b.is_vert() => {
                    to_check.push(Beam { pos, dir: (-1, 0) });
                    to_check.push(Beam { pos, dir: (1, 0) });
                }
                '-' if b.is_vert() => {
                    to_check.push(Beam { pos, dir: (0, -1) });
                    to_check.push(Beam { pos, dir: (0, 1) });
                }
                _ => to_check.push(Beam { pos, dir: b.dir }),
            }
        }
        energized.len() - 1 // the light came from out of the region.
    }
}
