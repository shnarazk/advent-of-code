//! <https://adventofcode.com/2015/day/15>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Ingredient {
    name: String,
    capacity: isize,
    durability: isize,
    flavor: isize,
    texture: isize,
    calories: isize,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Ingredient>,
}

mod parser {
    use {
        super::Ingredient,
        crate::parser::parse_isize,
        winnow::{
            ascii::{alpha1, newline},
            combinator::{separated, seq},
            ModalResult, Parser,
        },
    };

    fn parse_ingredient(s: &mut &str) -> ModalResult<Ingredient> {
        seq!(alpha1, _: ": capacity ", parse_isize, _: ", durability ", parse_isize, _: ", flavor ", parse_isize, _: ", texture ", parse_isize, _: ", calories ", parse_isize)
            .map(
                |(name, capacity, durability, flavor, texture, calories)| Ingredient {
                    name: name.to_string(),
                    capacity,
                    durability,
                    flavor,
                    texture,
                    calories,
                },
            )
            .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Ingredient>> {
        separated(1.., parse_ingredient, newline).parse_next(s)
    }
}

#[aoc(2015, 15)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Self::parsed()
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
