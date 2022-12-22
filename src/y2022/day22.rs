//! <https://adventofcode.com/2022/day/22>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        color,
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{HashMap, HashSet},
};

type Dim2 = (usize, usize);
type Dir2 = (isize, isize);

type Map = (
    HashMap<Dim2, char>,
    HashMap<Dim2, Dim2>,
    HashMap<Dim2, Dim2>,
);

trait GeometricMove {
    fn position_to_move(&self, dir: &Dir2) -> Self;
}

impl GeometricMove for Dim2 {
    fn position_to_move(&self, dir: &Dir2) -> Self {
        (
            (self.0 as isize + dir.0) as usize,
            (self.1 as isize + dir.1) as usize,
        )
    }
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Direction {
    Go(usize),
    TurnLeft,
    TurnRight,
}

#[derive(Debug, Eq, PartialEq)]
struct Seeker {
    position: Dim2,
    direction: Dir2,
    trace: HashSet<Dim2>,
}

impl Default for Seeker {
    fn default() -> Self {
        Seeker {
            position: (0, 0),
            direction: (0, 1),
            trace: HashSet::new(),
        }
    }
}

impl Seeker {
    fn to_password(&self) -> usize {
        (self.position.0 + 1) * 1000
            + (self.position.1 + 1) * 4
            + match self.direction {
                (0, 1) => 0,
                (1, 0) => 1,
                (0, -1) => 2,
                (-1, 0) => 3,
                _ => unreachable!(),
            }
    }
    fn jump_to(&mut self, pos: &Dim2) {
        self.position = *pos;
        self.trace.insert(self.position);
    }
    fn go_forward(&mut self) {
        self.position = self.position.position_to_move(&self.direction);
        self.trace.insert(self.position);
    }
    fn horizontal(&self) -> bool {
        self.direction.1 != 0
    }
    fn turn_right(&mut self) {
        self.direction = match self.direction {
            (0, 1) => (1, 0),
            (1, 0) => (0, -1),
            (0, -1) => (-1, 0),
            (-1, 0) => (0, 1),
            _ => unreachable!(),
        }
    }
    fn turn_left(&mut self) {
        self.direction = match self.direction {
            (0, 1) => (-1, 0),
            (1, 0) => (0, 1),
            (0, -1) => (1, 0),
            (-1, 0) => (0, -1),
            _ => unreachable!(),
        }
    }
    fn next_position(&self) -> Dim2 {
        self.position.position_to_move(&self.direction)
    }
    fn step(&mut self, map: &Map, direction: &Direction) {
        match direction {
            Direction::Go(steps) => {
                for _ in 0..*steps {
                    let next = self.next_position();
                    if let Some(land) = map.0.get(&next) {
                        match land {
                            '.' => self.go_forward(),
                            '#' => break,
                            _ => unreachable!(),
                        }
                    } else if let Some(pos) = if self.horizontal() {
                        map.1.get(&self.position)
                    } else {
                        map.2.get(&self.position)
                    } {
                        match map.0.get(pos) {
                            Some(&'.') => {
                                self.jump_to(pos);
                                // println!("jump to {:?}", self.position);
                            }
                            Some(&'#') => {
                                break;
                            }
                            _ => unreachable!(),
                        }
                    } else {
                        for k in map
                            .1
                            .keys()
                            .filter(|(j, i)| *j == self.position.0 || *i == self.position.1)
                        {
                            println!("jump table points {k:?}");
                        }
                        panic!();
                    }
                    assert!(map.0.get(&self.position) == Some(&'.'));
                }
                assert!(map.0.get(&self.position) == Some(&'.'));
            }
            Direction::TurnLeft => {
                self.turn_left();
            }
            Direction::TurnRight => {
                self.turn_right();
            }
        }
        assert!(map.0.get(&self.position) == Some(&'.'));
        // println!("{:?}:{:?}", self.position, self.direction);
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    map: HashMap<Dim2, char>,
    ring_h: HashMap<Dim2, Dim2>,
    ring_v: HashMap<Dim2, Dim2>,
    path: Vec<Direction>,
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
            let mut buffer = block;
            let num_parser = regex!(r"^(\d+)");
            let turn_parser = regex!(r"^(L|R)");
            loop {
                if let Some(segment) = num_parser.captures(buffer) {
                    self.path.push(Direction::Go(segment[1].parse::<usize>()?));
                    buffer = &buffer[segment[1].len()..];
                    continue;
                }
                if let Some(segment) = turn_parser.captures(buffer) {
                    if &segment[1] == "L" {
                        self.path.push(Direction::TurnLeft);
                    } else {
                        self.path.push(Direction::TurnRight);
                    }
                    buffer = &buffer[segment[1].len()..];
                    continue;
                }
                dbg!(buffer);
                break;
            }
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        for (j, l) in self.line.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                if *c != ' ' {
                    self.map.insert((j, i), *c);
                }
            }
        }
        // build the edge map horizontally
        for (j, l) in self.line.iter().enumerate() {
            let width = l.len();
            let mut start = None;
            let mut end = None;
            for (i, _) in l.iter().enumerate() {
                if self.map.get(&(j, i)).is_some() {
                    start = start.or(Some(i));
                } else if start.is_some() {
                    end = end.or(Some(i));
                }
                if end.is_some() {
                    break;
                }
            }
            end = end.or(Some(width));
            if let (Some(s), Some(e)) = (start, end) {
                self.ring_h.insert((j, s), (j, e - 1));
                self.ring_h.insert((j, e - 1), (j, s));
            } else {
                panic!();
            }
        }
        // build the edge map vertically
        let mut min_y: HashMap<usize, usize> = HashMap::new();
        let mut max_y: HashMap<usize, usize> = HashMap::new();
        let mut max_width = 0;
        for (j, l) in self.line.iter().enumerate() {
            for (i, c) in l.iter().enumerate() {
                max_width = max_width.max(i);
                if self.map.get(&(j, i)).is_some() {
                    let e_min = min_y.entry(i).or_insert(usize::MAX);
                    *e_min = (*e_min).min(j);
                    let e_max = max_y.entry(i).or_insert(0);
                    *e_max = (*e_max).max(j);
                }
            }
        }
        for i in 0..=max_width {
            let start = min_y.get(&i);
            let end = max_y.get(&i);
            if let (Some(s), Some(e)) = (start, end) {
                self.ring_v.insert((*s, i), (*e, i));
                self.ring_v.insert((*e, i), (*s, i));
            } else {
                panic!();
            }
        }
        dbg!(&self.line.len());
        dbg!(&self.map.len());
        dbg!(&self.ring_h.len());
        dbg!(&self.ring_v.len());
        dbg!(&self.path.len());
    }
    fn dump(&self) {
        let start = self.map.keys().min().unwrap();
        let mut seeker = Seeker {
            position: *start,
            ..Default::default()
        };
        let map = (self.map.clone(), self.ring_h.clone(), self.ring_v.clone());
        for d in self.path.iter() {
            seeker.step(&map, d);
        }
        let h = self.line.len();
        let w = self.line.iter().map(|l| l.len()).max().unwrap_or_default();
        for j in 0..h {
            for i in 0..w {
                if seeker.trace.contains(&(j, i)) {
                    print!(
                        "{}{}{}",
                        color::REVERSE,
                        self.map.get(&(j, i)).unwrap_or(&' '),
                        color::RESET
                    );
                } else if self.ring_h.contains_key(&(j, i)) || self.ring_v.contains_key(&(j, i)) {
                    print!(
                        "{}{}{}",
                        color::RED,
                        self.map.get(&(j, i)).unwrap_or(&' '),
                        color::RESET
                    );
                } else {
                    print!("{}", self.map.get(&(j, i)).unwrap_or(&' '));
                }
            }
            println!();
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        let start = self.map.keys().min().unwrap();
        // dbg!(&start);
        let mut seeker = Seeker {
            position: *start,
            ..Default::default()
        };
        let map = (self.map.clone(), self.ring_h.clone(), self.ring_v.clone());
        for d in self.path.iter() {
            seeker.step(&map, d);
        }
        // dbg!(&seeker);
        seeker.to_password()
    }
    fn part2(&mut self) -> Self::Output2 {
        2
    }
}
