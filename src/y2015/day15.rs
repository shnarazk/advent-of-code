//! <https://adventofcode.com/2015/day/15>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    line_parser, regex,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Ingredient {
    name: String,
    capacity: isize,
    durability: isize,
    flavor: isize,
    texture: isize,
    calories: isize,
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Ingredient>,
}

#[aoc(2015, 15)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(
            r"^([A-Za-z]+): capacity (-?[0-9]+), durability (-?[0-9]+), flavor (-?[0-9]+), texture (-?[0-9]+), calories (-?[0-9]+)$"
        );
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push(Ingredient {
            name: segment[1].to_string(),
            capacity: line_parser::to_isize(&segment[2])?,
            durability: line_parser::to_isize(&segment[3])?,
            flavor: line_parser::to_isize(&segment[4])?,
            texture: line_parser::to_isize(&segment[5])?,
            calories: line_parser::to_isize(&segment[6])?,
        });
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut rank_max: usize = 0;
        let n = self.line.len();
        if n == 2 {
            for n1 in 0..=100 {
                for n2 in 0..=100 {
                    if n1 + n2 != 100 {
                        continue;
                    }
                    let vec = vec![n1, n2];
                    let r = self.rank(&vec);
                    if rank_max < r {
                        rank_max = r;
                    }
                }
            }
        }
        if n == 4 {
            for n0 in 0..=100 {
                for n1 in 0..=100 {
                    for n2 in 0..=100 {
                        for n3 in 0..=100 {
                            if n0 + n1 + n2 + n3 != 100 {
                                continue;
                            }
                            let vec = vec![n0, n1, n2, n3];
                            let r = self.rank(&vec);
                            if rank_max < r {
                                rank_max = r;
                            }
                        }
                    }
                }
            }
        }
        rank_max
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut rank_max: usize = 0;
        let n = self.line.len();
        if n == 2 {
            for n1 in 0..=100 {
                for n2 in 0..=100 {
                    if n1 + n2 != 100 {
                        continue;
                    }
                    let vec = vec![n1, n2];
                    let r = self.rank(&vec);
                    if self.calorie(&vec) == 500 && rank_max < r {
                        rank_max = r;
                    }
                }
            }
        }
        if n == 4 {
            for n0 in 0..=100 {
                for n1 in 0..=100 {
                    for n2 in 0..=100 {
                        for n3 in 0..=100 {
                            if n0 + n1 + n2 + n3 != 100 {
                                continue;
                            }
                            let vec = vec![n0, n1, n2, n3];
                            let r = self.rank(&vec);
                            if self.calorie(&vec) == 500 && rank_max < r {
                                rank_max = r;
                            }
                        }
                    }
                }
            }
        }
        rank_max
    }
}

impl Puzzle {
    fn rank(&self, vec: &[usize]) -> usize {
        let results = (0..4_isize)
            .map(|i| {
                self
                 .line.iter()
                 .zip(vec.iter())
                 .map(|(ing, n)|
                      match i {
                          0 => ing.capacity,
                          1 => ing.durability,
                          2 => ing.flavor,
                          3 => ing.texture,
                          _ => unreachable!(),
                      } * (*n as isize)
                 )
                 .sum::<isize>().max(0)
            })
            .collect::<Vec<_>>();
        results.iter().product::<isize>().max(0) as usize
    }
    fn calorie(&self, vec: &[usize]) -> isize {
        self.line
            .iter()
            .zip(vec.iter())
            .map(|(ing, n)| ing.calories * (*n as isize))
            .sum::<isize>()
    }
}
