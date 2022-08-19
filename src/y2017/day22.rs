//! <https://adventofcode.com/2017/day/22>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashSet,
};

type Location = (isize, isize);
const UP: Location = (-1, 0);
const RIGHT: Location = (0, 1);
const DOWN: Location = (1, 0);
const LEFT: Location = (0, -1);

fn rotate_cw(dir: Location) -> Location {
    match dir {
        UP => RIGHT,
        RIGHT => DOWN,
        DOWN => LEFT,
        LEFT => UP,
        _ => unreachable!(),
    }
}

fn rotate_ccw(dir: Location) -> Location {
    match dir {
        RIGHT => UP,
        DOWN => RIGHT,
        LEFT => DOWN,
        UP => LEFT,
        _ => unreachable!(),
    }
}

fn turn_to(dir: Location, infected: bool) -> Location {
    if infected {
        rotate_cw(dir)
    } else {
        rotate_ccw(dir)
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
    infection_map: HashSet<Location>,
}

#[aoc(2017, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c == '#').collect::<Vec<_>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(self.line.len());
        for (j, line) in self.line.iter().enumerate() {
            for (i, b) in line.iter().enumerate() {
                if *b {
                    self.infection_map.insert((j as isize, i as isize));
                }
            }
        }
        dbg!(self.infection_map.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let len = self.line.len();
        let mut carrier_position: Location = ((len / 2) as isize, (len / 2) as isize);
        let mut carrier_direction: Location = UP;
        let mut infects = 0;
        self.render();
        for step in 0..10000 {
            let mode = self.infection_map.contains(&carrier_position);
            carrier_direction = turn_to(carrier_direction, mode);
            if mode {
                self.infection_map.remove(&carrier_position);
            } else {
                infects += 1;
                self.infection_map.insert(carrier_position);
            }
            carrier_position.0 += carrier_direction.0;
            carrier_position.1 += carrier_direction.1;
            // println!("{step}");
            // self.render();
        }
        infects
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

impl Puzzle {
    fn render(&self) {
        for j in -3..6_isize {
            for i in -3..6_isize {
                print!(
                    "{}",
                    if self.infection_map.contains(&(j, i)) {
                        '#'
                    } else {
                        '.'
                    }
                );
            }
            println!();
        }
    }
}
