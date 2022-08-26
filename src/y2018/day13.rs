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
    let dirs = [(1, 0), (0, 1), (-1, 0), (0, -1)];
    for (i, d) in dirs.iter().enumerate() {
        if *d == dir {
            return dirs[(i + 5 - 2 * (right as usize)) % 4];
        }
    }
    unreachable!()
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
    type Output2 = usize;
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
        dbg!(self.cart.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        // self.render();
        for _ in 0.. {
            self.update();
            // self.render();
            if let Some(clash) = self.check() {
                return format!("{},{}", clash.1, clash.0);
            }
        }
        unreachable!()
    }
    fn part2(&mut self) -> Self::Output2 {
        0
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
        }
    }
    fn render(&self) {
        for (y, l) in self.line.iter().enumerate() {
            for (x, c) in l.iter().enumerate() {
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
}
