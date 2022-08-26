//! <https://adventofcode.com/2018/day/13>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{HashMap, HashSet},
};

type Dim2 = (isize, isize);

fn turn_dim2(dir: Dim2, right: bool) -> Dim2 {
    let dirs = [(-1, 0), (0, 1), (1, 0), (0, -1)];
    for (i, d) in dirs.iter().enumerate() {
        if *d == dir {
            return dirs[(i + 3 + 2 * (right as usize)) % 4];
        }
    }
    unreachable!()
}

#[test]
fn y2018day13_turn() {
    assert_eq!(turn_dim2((-1, 0), true), (0, 1));
    assert_eq!(turn_dim2((-1, 0), false), (0, -1));
    assert_eq!(turn_dim2((0, -1), true), (-1, 0));
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Cart {
    location: Dim2,
    direction: Dim2,
    turn_num: usize,
}

impl Cart {
    fn turn(&mut self) {
        match self.turn_num % 3 {
            0 => self.direction = turn_dim2(self.direction, false),
            1 => (),
            2 => self.direction = turn_dim2(self.direction, true),
            _ => unreachable!(),
        }
        self.turn_num += 1;
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    cart: Vec<Cart>,
    map: HashMap<Dim2, u8>,
}

#[aoc_at(2018, 13)]
impl AdventOfCode for Puzzle {
    type Output1 = String;
    type Output2 = String;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line
            .push(block.chars().map(|c| c as u8).collect::<Vec<u8>>());
        Ok(())
    }
    fn after_insert(&mut self) {
        for (y, l) in self.line.iter_mut().enumerate() {
            for (x, c) in l.iter_mut().enumerate() {
                match c {
                    b'<' => {
                        self.map.insert((y as isize, x as isize), b'S');
                        self.cart.push(Cart {
                            location: (y as isize, x as isize),
                            direction: (0, -1),
                            turn_num: 0,
                        });
                        *c = b'-';
                    }
                    b'>' => {
                        self.map.insert((y as isize, x as isize), b'S');
                        self.cart.push(Cart {
                            location: (y as isize, x as isize),
                            direction: (0, 1),
                            turn_num: 0,
                        });
                        *c = b'-';
                    }
                    b'^' => {
                        self.map.insert((y as isize, x as isize), b'S');
                        self.cart.push(Cart {
                            location: (y as isize, x as isize),
                            direction: (-1, 0),
                            turn_num: 0,
                        });
                        *c = b'|';
                    }
                    b'v' => {
                        self.map.insert((y as isize, x as isize), b'S');
                        self.cart.push(Cart {
                            location: (y as isize, x as isize),
                            direction: (1, 0),
                            turn_num: 0,
                        });
                        *c = b'|';
                    }
                    b'-' | b'|' => {
                        self.map.insert((y as isize, x as isize), b'S');
                    }
                    b'/' => {
                        self.map.insert((y as isize, x as isize), b'T'); // tokei-mawari from vertical segment
                    }
                    b'\\' => {
                        self.map.insert((y as isize, x as isize), b'H'); // han-tokei-mawari from vertical segment
                    }
                    b'+' => {
                        self.map.insert((y as isize, x as isize), b'I');
                    }
                    _ => (),
                }
            }
        }
        dbg!(self.line.len(), self.line[0].len(), self.cart.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        // self.render();
        for _ in 0.. {
            self.render();
            self.update();
            if let Some(clash) = self.check() {
                self.render();
                return format!("{},{}", clash.1, clash.0);
            }
        }
        unreachable!()
    }
    fn part2(&mut self) -> Self::Output2 {
        for step in 0.. {
            if let Some(last) = self.update2() {
                return format!("{},{} at {}", last.1, last.0, step);
            }
        }
        unreachable!()
    }
}

impl Puzzle {
    fn update(&mut self) {
        for c in self.cart.iter_mut() {
            match self.map.get(&c.location) {
                Some(b'S') => {}
                Some(b'T') => {
                    c.direction = turn_dim2(c.direction, c.direction.0 != 0);
                }
                Some(b'H') => {
                    c.direction = turn_dim2(c.direction, c.direction.1 != 0);
                }
                Some(b'I') => {
                    c.turn();
                }
                _ => unreachable!(),
            }
            c.location = (c.location.0 + c.direction.0, c.location.1 + c.direction.1);
            assert!(self.map.get(&c.location).is_some());
        }
    }
    fn render(&self) {
        for (y, l) in self.line.iter().enumerate() {
            if 59 < y {
                continue;
            }
            for (x, c) in l.iter().enumerate() {
                if 147 < x {
                    continue;
                }
                print!(
                    "{}",
                    if self
                        .cart
                        .iter()
                        .any(|c| c.location == (y as isize, x as isize))
                    {
                        'C'
                    } else {
                        *c as char
                    },
                );
            }
            println!();
        }
    }
    fn check(&self) -> Option<Dim2> {
        let mut pos: HashSet<Dim2> = HashSet::new();
        for c in self.cart.iter() {
            if pos.contains(&c.location) {
                return Some(c.location);
            }
            pos.insert(c.location);
        }
        None
    }
    fn update2(&mut self) -> Option<Dim2> {
        const DEAD: Dim2 = (0, 0);
        self.cart.sort();
        for i in 0..self.cart.len() {
            if self.cart[i].direction == DEAD {
                continue;
            }
            match self.map.get(&self.cart[i].location) {
                Some(b'S') => {}
                Some(b'T') => {
                    self.cart[i].direction =
                        turn_dim2(self.cart[i].direction, self.cart[i].direction.0 != 0);
                }
                Some(b'H') => {
                    self.cart[i].direction =
                        turn_dim2(self.cart[i].direction, self.cart[i].direction.1 != 0);
                }
                Some(b'I') => {
                    self.cart[i].turn();
                }
                _ => unreachable!(),
            }
            self.cart[i].location = (
                self.cart[i].location.0 + self.cart[i].direction.0,
                self.cart[i].location.1 + self.cart[i].direction.1,
            );
            for j in 0..self.cart.len() {
                if i == j {
                    continue;
                }
                if self.cart[j].direction == DEAD {
                    continue;
                }
                if self.cart[i].location == self.cart[j].location {
                    self.cart[i].direction = DEAD;
                    self.cart[j].direction = DEAD;
                }
            }
        }
        let m = self.cart.len();
        self.cart.retain(|c| c.direction != DEAD);
        let n = self.cart.len();
        if m != n {
            dbg!(self.cart.len());
        }
        (self.cart.len() == 1).then(|| self.cart[0].location)
    }
    fn check2(&mut self) -> Option<Dim2> {
        let mut pos: HashMap<Dim2, usize> = HashMap::new();
        for c in self.cart.iter_mut() {
            *pos.entry(c.location).or_insert(0) += 1;
        }
        assert!(pos.values().all(|v| *v < 3));
        let n = self.cart.len();
        self.cart.retain(|c| pos.get(&c.location) == Some(&1));
        assert!(!self.cart.is_empty());
        (self.cart.len() == 1).then(|| self.cart[0].location)
    }
}
