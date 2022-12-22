//! <https://adventofcode.com/2022/day/22>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashMap,
};

type Dim2 = (usize, usize);
type Map = (HashMap<Dim2, char>, HashMap<Dim2, Dim2>);

trait GeometricMove {
    fn position_to_move(&self, dir: &Self) -> Self;
}

impl GeometricMove for Dim2 {
    fn position_to_move(&self, dir: &Self) -> Self {
        (self.0 + dir.0, self.1 + dir.1)
    }
}

struct Seeker {
    position: Dim2,
    direction: Dim2,
}

impl Default for Seeker {
    fn default() -> Self {
        Seeker {
            position: (0, 0),
            direction: (0, 1),
        }
    }
}

impl Seeker {
    fn next_position(&self) -> Dim2 {
        self.position.position_to_move(&self.direction)
    }
    fn step(&mut self, map: &Map, direction: (char, usize)) {
        for _ in 0..direction.1 {
            let pos = self.next_position();
            if let Some(land) = map.0.get(&pos) {
                match land {
                    '.' => self.position = pos,
                    '#' => break,
                    _ => unreachable!(),
                }
            } else if let Some(pos) = map.1.get(&self.position) {
                self.position = *pos;
            }
        }
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    map: HashMap<Dim2, char>,
    edge: HashMap<Dim2, Dim2>,
    loaded_map: Vec<Vec<char>>,
    line: Vec<Vec<char>>,
}

#[aoc(2022, 22)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let v = block.chars().collect::<Vec<_>>();
        if v.iter().any(|c| [' ', '.', '#'].contains(c)) {
            self.line.push(v);
        } else {
            self.loaded_map.push(v);
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        for (j, l) in self.loaded_map.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                if *c != '.' {
                    self.map.insert((j, i), *c);
                }
            }
        }
        // build the edge map horizontally
        for (j, l) in self.loaded_map.iter().enumerate() {
            let mut start = None;
            let mut end = None;
            for (i, c) in l.iter().enumerate() {
                if self.map.get(&(j, i)).is_some() {
                    start = start.or(Some(j));
                } else {
                    end = end.or(Some(i));
                }
                if end.is_some() {
                    break;
                }
            }
            self.edge.insert((j, start.unwrap()), (j, end.unwrap() - 1));
            self.edge.insert((j, end.unwrap() - 1), (j, start.unwrap()));
        }
        // build the edge map vertically
        let mut min_y: HashMap<usize, usize> = HashMap::new();
        let mut max_y: HashMap<usize, usize> = HashMap::new();
        for (j, l) in self.loaded_map.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                let e_min = min_y.entry(i).or_insert(0);
                *e_min = (*e_min).min(j);
                let e_max = max_y.entry(i).or_insert(0);
                *e_max = (*e_max).min(j);
            }
        }
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        1
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
