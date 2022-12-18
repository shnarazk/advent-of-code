//! <https://adventofcode.com/2022/day/18>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric, line_parser, regex,
    },
    std::collections::HashSet,
};

const L: usize = 100;
const OFFSET: usize = 10;
type Dim3 = (usize, usize, usize);

#[derive(Default, Debug, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
    map: HashSet<Dim3>,
}

#[aoc(2022, 18)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        // let parser = regex!(r"^(\d+)$");
        // let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push(line_parser::to_usizes(block, ',')?);
        Ok(())
    }
    fn after_insert(&mut self) {
        for dim3 in self.line.iter_mut() {
            // the real data contains values that require isize. So give them offsets!
            dim3[0] += OFFSET;
            dim3[1] += OFFSET;
            dim3[2] += OFFSET;
            assert!(0 < dim3[0] && dim3[0] < L, "{}", dim3[0]);
            assert!(0 < dim3[1] && dim3[1] < L, "{}", dim3[1]);
            assert!(0 < dim3[2] && dim3[2] < L, "{}", dim3[2]);
            self.map.insert((dim3[0], dim3[1], dim3[2]));
        }
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        self.map
            .iter()
            .map(|pos| {
                geometric::cubic_neighbors6(pos.0, pos.1, pos.2, L, L, L)
                    .iter()
                    .filter(|p| !self.map.contains(p))
                    .count()
            })
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        type Surface = (Dim3, usize);
        let mut visited_surfaces: HashSet<Surface> = HashSet::new();
        let mut to_visit: Vec<Surface> = Vec::new();
        let c = self.map.iter().min().unwrap();
        let start = (*c, 5);
        println!("{:?}", &start);
        to_visit.push(start);
        visited_surfaces.insert(start);

        while let Some(s) = to_visit.pop() {
            // if visited_surfaces.contains(&s) {
            //     continue;
            // }
            // visited_surfaces.insert(s);
            let edges = match s.1 {
                0 => [
                    [
                        ((s.0.0_ + 1, s.0.1_ + 1, s.0.2_____), 3),
                        ((s.0.0_____, s.0.1_ + 1, s.0.2_____), 0),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 2),
                    ],
                    [
                        ((s.0.0_ + 1, s.0 .1 - 1, s.0.2_____), 2),
                        ((s.0.0_____, s.0 .1 - 1, s.0.2_____), 0),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 3),
                    ],
                    [
                        ((s.0.0_ + 1, s.0.1_____, s.0.2_ + 1), 5),
                        ((s.0.0_____, s.0.1_____, s.0.2_ + 1), 0),
                        ((s.0.0_____, s.0.1_____, s.0.2_ + 1), 4),
                    ],
                    [
                        ((s.0.0_ + 1, s.0.1_____, s.0 .2 - 1), 4),
                        ((s.0.0_____, s.0.1_____, s.0 .2 - 1), 0),
                        ((s.0.0_____, s.0.1_____, s.0 .2 - 1), 5),
                    ],
                ],
                1 => [
                    [
                        ((s.0.0_ - 1, s.0.1_ + 1, s.0.2_____), 3),
                        ((s.0.0_____, s.0.1_ + 1, s.0.2_____), 1),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 2),
                    ],
                    [
                        ((s.0.0_ - 1, s.0.1_ - 1, s.0.2_____), 2),
                        ((s.0.0_____, s.0.1_ - 1, s.0.2_____), 1),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 3),
                    ],
                    [
                        ((s.0.0_ - 1, s.0.1_____, s.0.2_ + 1), 5),
                        ((s.0.0_____, s.0.1_____, s.0.2_ + 1), 1),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 4),
                    ],
                    [
                        ((s.0.0_ - 1, s.0.1_____, s.0.2_ - 1), 4),
                        ((s.0.0_____, s.0.1_____, s.0.2_ - 1), 1),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 5),
                    ],
                ],
                2 => [
                    [
                        ((s.0.0_ + 1, s.0.1_ + 1, s.0.2_____), 1),
                        ((s.0.0_ + 1, s.0.1_____, s.0.2_____), 2),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 0),
                    ],
                    [
                        ((s.0.0_ - 1, s.0.1_ + 1, s.0.2_____), 0),
                        ((s.0.0_ - 1, s.0.1_____, s.0.2_____), 2),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 1),
                    ],
                    [
                        ((s.0.0_____, s.0.1_ + 1, s.0.2_ + 1), 5),
                        ((s.0.0_____, s.0.1_____, s.0.2_ + 1), 2),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 4),
                    ],
                    [
                        ((s.0.0_____, s.0.1_ + 1, s.0.2_ - 1), 4),
                        ((s.0.0_____, s.0.1_____, s.0.2_ - 1), 2),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 5),
                    ],
                ],
                3 => [
                    [
                        ((s.0.0_ + 1, s.0.1_ - 1, s.0.2_____), 1),
                        ((s.0.0_ + 1, s.0.1_____, s.0.2_____), 3),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 0),
                    ],
                    [
                        ((s.0.0_ - 1, s.0.1_ - 1, s.0.2_____), 0),
                        ((s.0.0_ - 1, s.0.1_____, s.0.2_____), 3),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 1),
                    ],
                    [
                        ((s.0.0_____, s.0.1_ - 1, s.0.2_ + 1), 5),
                        ((s.0.0_____, s.0.1_____, s.0.2_ + 1), 3),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 4),
                    ],
                    [
                        ((s.0.0_____, s.0.1_ - 1, s.0.2_ - 1), 4),
                        ((s.0.0_____, s.0.1_____, s.0.2_ - 1), 3),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 5),
                    ],
                ],
                4 => [
                    [
                        ((s.0.0_ + 1, s.0.1_____, s.0.2_ + 1), 1),
                        ((s.0.0_ + 1, s.0.1_____, s.0.2_____), 4),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 0),
                    ],
                    [
                        ((s.0.0_ - 1, s.0.1_____, s.0.2_ + 1), 0),
                        ((s.0.0_ - 1, s.0.1_____, s.0.2_____), 4),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 1),
                    ],
                    [
                        ((s.0.0_____, s.0.1_ + 1, s.0.2_ + 1), 3),
                        ((s.0.0_____, s.0.1_ + 1, s.0.2_____), 4),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 2),
                    ],
                    [
                        ((s.0.0_____, s.0.1_ - 1, s.0.2_ + 1), 2),
                        ((s.0.0_____, s.0.1_ - 1, s.0.2_____), 4),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 3),
                    ],
                ],
                5 => [
                    [
                        ((s.0.0_ + 1, s.0.1_____, s.0.2_ - 1), 1),
                        ((s.0.0_ + 1, s.0.1_____, s.0.2_____), 5),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 0),
                    ],
                    [
                        ((s.0.0_ - 1, s.0.1_____, s.0.2_ - 1), 0),
                        ((s.0.0_ - 1, s.0.1_____, s.0.2_____), 5),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 1),
                    ],
                    [
                        ((s.0.0_____, s.0.1_ + 1, s.0.2_ - 1), 3),
                        ((s.0.0_____, s.0.1_ + 1, s.0.2_____), 5),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 2),
                    ],
                    [
                        ((s.0.0_____, s.0.1_ - 1, s.0.2_ - 1), 2),
                        ((s.0.0_____, s.0.1_ - 1, s.0.2_____), 5),
                        ((s.0.0_____, s.0.1_____, s.0.2_____), 3),
                    ],
                ],
                _ => unreachable!(),
            };
            for edge in edges.iter() {
                for target in edge.iter() {
                    if self.map.contains(&target.0) {
                        if !visited_surfaces.contains(target) {
                            println!(
                                "({:>2},{:>2},{:>2}) @ {} => ({:>2},{:>2},{:>2}) @ {}",
                                s.0 .0 - OFFSET,
                                s.0 .1 - OFFSET,
                                s.0 .2 - OFFSET,
                                s.1,
                                target.0 .0 - OFFSET,
                                target.0 .1 - OFFSET,
                                target.0 .2 - OFFSET,
                                target.1
                            );
                            to_visit.push(*target);
                            visited_surfaces.insert(*target);
                        }
                        break;
                    }
                }
            }
        }
        visited_surfaces.len()
    }
}
