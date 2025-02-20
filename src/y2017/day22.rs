//! <https://adventofcode.com/2017/day/22>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::{HashMap, HashSet},
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
        rotate_cw(dir) // right
    } else {
        rotate_ccw(dir) // left
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
enum Mode2 {
    #[default]
    Clean,
    Weakened,
    Infected,
    Flagged,
}

impl Mode2 {
    fn shift(&self) -> Mode2 {
        match self {
            Mode2::Clean => Mode2::Weakened,
            Mode2::Weakened => Mode2::Infected,
            Mode2::Infected => Mode2::Flagged,
            Mode2::Flagged => Mode2::Clean,
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<bool>>,
    infection_map: HashSet<Location>,
    infection_map2: HashMap<Location, Mode2>,
}

#[aoc(2017, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn parse_block(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c == '#').collect::<Vec<_>>());
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(self.line.len());
        for (j, line) in self.line.iter().enumerate() {
            for (i, b) in line.iter().enumerate() {
                if *b {
                    self.infection_map.insert((j as isize, i as isize));
                    self.infection_map2
                        .insert((j as isize, i as isize), Mode2::Infected);
                }
            }
        }
        // dbg!(self.infection_map.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let len = self.line.len();
        let mut carrier_position: Location = ((len / 2) as isize, (len / 2) as isize);
        let mut carrier_direction: Location = UP;
        let mut infects = 0;
        // self.render();
        for _ in 0..10000 {
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
        let len = self.line.len();
        let mut carrier_position: Location = ((len / 2) as isize, (len / 2) as isize);
        let mut carrier_direction: Location = UP;
        let mut infects = 0;
        // self.render2();
        for _ in 0..10_000_000 {
            let mode: &Mode2 = self
                .infection_map2
                .get(&carrier_position)
                .unwrap_or(&Mode2::Clean);
            match mode {
                Mode2::Clean => {
                    carrier_direction = turn_to(carrier_direction, false); // left
                    self.infection_map2.insert(carrier_position, mode.shift());
                }
                Mode2::Weakened => {
                    self.infection_map2.insert(carrier_position, mode.shift());
                    infects += 1;
                }
                Mode2::Infected => {
                    carrier_direction = turn_to(carrier_direction, true); // right
                    self.infection_map2.insert(carrier_position, mode.shift());
                }
                Mode2::Flagged => {
                    carrier_direction = turn_to(carrier_direction, true);
                    carrier_direction = turn_to(carrier_direction, true);
                    self.infection_map2.remove(&carrier_position);
                }
            }
            carrier_position.0 += carrier_direction.0;
            carrier_position.1 += carrier_direction.1;
            // println!("{:?}@{step}", carrier_position);
            // self.render2();
        }
        infects
    }
}

#[allow(dead_code)]
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
    fn render2(&self) {
        for j in -3..5_isize {
            for i in -3..6_isize {
                print!(
                    "{}",
                    match self.infection_map2.get(&(j, i)) {
                        Some(Mode2::Clean) | None => '.',
                        Some(Mode2::Weakened) => 'W',
                        Some(Mode2::Infected) => '#',
                        Some(Mode2::Flagged) => 'F',
                    }
                );
            }
            println!();
        }
    }
}
