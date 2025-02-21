//! <https://adventofcode.com/2021/day/17>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<(isize, isize, isize, isize)>,
}

mod parser {
    use {
        crate::parser::parse_isize,
        winnow::{ModalResult, Parser, combinator::seq},
    };

    pub fn parse(s: &mut &str) -> ModalResult<(isize, isize, isize, isize)> {
        seq!(
            _: "target area: x=",
            parse_isize,
             _: "..",
            parse_isize,
            _: ", y=",
            parse_isize,
            _: "..",
            parse_isize,
        )
        .parse_next(s)
    }
}

#[aoc(2021, 17)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        let (x1, x2, y1, y2) = parser::parse(&mut input)?;
        self.line
            .push((y1.max(y2), y1.min(y2), x1.min(x2), x1.max(x2)));
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut result: isize = 0;
        for (y1, y2, x1, x2) in self.line.iter() {
            let mut init_sy;
            'next: for init_sx in 1_isize..=*x2 {
                for y in 1_isize..(x2.abs() + y2.abs()) {
                    init_sy = y;
                    let mut sy = init_sy;
                    let mut sx = init_sx;
                    // println!("trace: {},{}", init_sy, init_sx);
                    let mut depth: isize = init_sy;
                    let mut dist: isize = init_sx;
                    while *y1 < depth || dist < *x1 {
                        // print!("({}, {})|{}->", depth, dist, sx);
                        if sx == 0 && dist < *x1 {
                            // println!(
                            //     "skip to next of init_sx = {} at ({}, {})",
                            //     init_sx, depth, dist,
                            // );
                            continue 'next;
                        }
                        sx = (sx - 1).max(0);
                        sy -= 1;
                        dist += sx;
                        depth += sy;
                    }
                    if depth < *y2 && *x2 < dist {
                        break;
                    }
                    // assert!(!(init_sy == 2 && init_sx == 7));
                    // println!("at ({}, {}) by ({}, {})", depth, dist, init_sy, init_sx);
                    if *y2 <= depth && dist <= *x2 {
                        // println!("- found {}, {}", init_sy, init_sx);
                        // simulate again
                        let mut sy = init_sy;
                        let mut max_height: isize = 0;
                        let mut height: isize = init_sy;
                        while max_height < height {
                            max_height = height;
                            sy -= 1;
                            height += sy;
                        }
                        result = result.max(max_height);
                    }
                }
                // println!("swipped at sx = {}, stoped at sy = {}", init_sx, init_sy);
            }
        }
        result.unsigned_abs()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut nsat: usize = 0;
        for (y1, y2, x1, x2) in self.line.iter() {
            let mut init_sy;
            'next: for init_sx in -*x2..=*x2 {
                for y in -(x2.abs() + y2.abs())..(x2.abs() + y2.abs()) {
                    init_sy = y;
                    let mut sy = init_sy;
                    let mut sx = init_sx;
                    let mut depth: isize = init_sy;
                    let mut dist: isize = init_sx;
                    while *y1 < depth || dist < *x1 {
                        // print!("({}, {})|{}->", depth, dist, sx);
                        if sx == 0 && dist < *x1 {
                            continue 'next;
                        }
                        sx = (sx - 1).max(0);
                        sy -= 1;
                        dist += sx;
                        depth += sy;
                    }
                    if depth < *y2 && *x2 < dist {
                        break;
                    }
                    // assert!(!(init_sy == 2 && init_sx == 7));
                    // println!("at ({}, {}) by ({}, {})", depth, dist, init_sy, init_sx);
                    if *y2 <= depth && dist <= *x2 {
                        // println!("- found {}, {}", init_sy, init_sx);
                        nsat += 1;
                    }
                }
            }
        }
        nsat
    }
}
