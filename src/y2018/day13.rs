//! <https://adventofcode.com/2018/day/13>
use {
    crate::framework::{aoc_at, AdventOfCode, ParseError},
    std::collections::HashMap,
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
    fn end_of_data(&mut self) {
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
        loop {
            // self.render();
            if let Some(clash) = self.update1() {
                // self.render();
                return format!("{},{}", clash.1, clash.0);
            }
        }
    }
    fn part2(&mut self) -> Self::Output2 {
        loop {
            if let Some(last) = self.update2() {
                return format!("{},{}", last.1, last.0);
            }
        }
    }
}

impl Puzzle {
    fn update1(&mut self) -> Option<Dim2> {
        self.cart.sort();
        for i in 0..self.cart.len() {
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
                if self.cart[i].location == self.cart[j].location {
                    return Some(self.cart[i].location);
                }
            }
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
    #[allow(dead_code)]
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
}
