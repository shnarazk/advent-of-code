//! <https://adventofcode.com/2020/day/12>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Clone, Debug, PartialEq)]
enum Dir {
    N,
    E,
    S,
    W,
}

impl Dir {
    fn left(&self) -> Self {
        match self {
            Dir::N => Dir::W,
            Dir::E => Dir::N,
            Dir::S => Dir::E,
            Dir::W => Dir::S,
        }
    }
    fn right(&self) -> Self {
        match self {
            Dir::N => Dir::E,
            Dir::E => Dir::S,
            Dir::S => Dir::W,
            Dir::W => Dir::N,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Instruction {
    N(usize),
    S(usize),
    E(usize),
    W(usize),
    L(usize),
    R(usize),
    F(usize),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Puzzle {
    codes: Vec<Instruction>,
    dir: Dir,
    waypoint_sn: isize,
    waypoint_we: isize,
    dist_sn: isize,
    dist_we: isize,
    ip: usize,
    mode: usize,
}

impl Default for Puzzle {
    fn default() -> Self {
        Puzzle {
            codes: Vec::new(),
            dir: Dir::E,
            waypoint_sn: 1,
            waypoint_we: 10,
            dist_sn: 0,
            dist_we: 0,
            ip: 0,
            mode: 0,
        }
    }
}

mod parser {
    use {
        super::Instruction,
        crate::parser::parse_usize,
        winnow::{
            ascii::newline,
            combinator::{alt, separated},
            PResult, Parser,
        },
    };

    fn parse_line(s: &mut &str) -> PResult<Instruction> {
        alt((
            ("N", parse_usize).map(|(_, n)| Instruction::N(n)),
            ("S", parse_usize).map(|(_, n)| Instruction::S(n)),
            ("E", parse_usize).map(|(_, n)| Instruction::E(n)),
            ("W", parse_usize).map(|(_, n)| Instruction::W(n)),
            ("L", parse_usize).map(|(_, n)| Instruction::L(n)),
            ("R", parse_usize).map(|(_, n)| Instruction::R(n)),
            ("F", parse_usize).map(|(_, n)| Instruction::F(n)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> PResult<Vec<Instruction>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2020, 12)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.codes = parser::parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn part1(&mut self) -> usize {
        self.mode = 1;
        self.run_program();
        self.distance()
    }
    fn part2(&mut self) -> usize {
        self.mode = 2;
        self.run_program();
        self.distance()
    }
}

impl Puzzle {
    fn distance(&self) -> usize {
        (self.dist_sn.unsigned_abs()) + (self.dist_we.unsigned_abs())
    }
    #[allow(dead_code)]
    fn print(&self) {
        if self.dist_we < 0 {
            print!("ship: west {} ", self.dist_we.abs());
        } else {
            print!("ship: east {} ", self.dist_we);
        }
        if self.dist_sn < 0 {
            print!("south {} ", self.dist_sn.abs());
        } else {
            print!("north {} ", self.dist_sn);
        }
        print!("facing {:?}, \t", self.dir);
        if self.waypoint_we < 0 {
            print!("waypoint west {} ", self.waypoint_we.abs());
        } else {
            print!("waypoint east {} ", self.waypoint_we);
        }
        if self.waypoint_sn < 0 {
            println!("south {} ", self.waypoint_sn.abs());
        } else {
            println!("north {} ", self.waypoint_sn);
        }
    }
    fn run_program(&mut self) {
        self.ip = 0;
        loop {
            if self.stopped() {
                return;
            }
            self.execute();
            // self.print();
        }
    }
    fn decode1(&mut self, inst: &Instruction) {
        match inst {
            Instruction::N(n) => {
                self.dist_sn += *n as isize;
            }
            Instruction::S(n) => {
                self.dist_sn -= *n as isize;
            }
            Instruction::E(n) => {
                self.dist_we += *n as isize;
            }
            Instruction::W(n) => {
                self.dist_we -= *n as isize;
            }
            Instruction::L(n) => match (n % 360) / 90 {
                0 => (),
                1 => self.dir = self.dir.left(),
                2 => self.dir = self.dir.left().left(),
                3 => self.dir = self.dir.right(),
                _ => panic!("can't handle"),
            },
            Instruction::R(n) => match (n % 360) / 90 {
                0 => (),
                1 => self.dir = self.dir.right(),
                2 => self.dir = self.dir.right().right(),
                3 => self.dir = self.dir.left(),
                _ => panic!("can't handle"),
            },
            Instruction::F(n) => match self.dir {
                Dir::N => self.dist_sn += *n as isize,
                Dir::E => self.dist_we += *n as isize,
                Dir::S => self.dist_sn -= *n as isize,
                Dir::W => self.dist_we -= *n as isize,
            },
        }
    }
    fn decode2(&mut self, inst: &Instruction) {
        match inst {
            Instruction::N(n) => {
                self.waypoint_sn += *n as isize;
            }
            Instruction::S(n) => {
                self.waypoint_sn -= *n as isize;
            }
            Instruction::E(n) => {
                self.waypoint_we += *n as isize;
            }
            Instruction::W(n) => {
                self.waypoint_we -= *n as isize;
            }
            Instruction::L(n) => {
                let sn = self.waypoint_sn;
                let we = self.waypoint_we;
                match (n % 360) / 90 {
                    0 => (),
                    1 => {
                        self.waypoint_sn = we;
                        self.waypoint_we = -sn;
                    }
                    2 => {
                        self.waypoint_sn = -sn;
                        self.waypoint_we = -we;
                    }
                    3 => {
                        self.waypoint_sn = -we;
                        self.waypoint_we = sn;
                    }
                    _ => panic!("can't handle"),
                }
            }
            Instruction::R(n) => {
                let sn = self.waypoint_sn;
                let we = self.waypoint_we;
                match (n % 360) / 90 {
                    0 => (),
                    1 => {
                        self.waypoint_sn = -we;
                        self.waypoint_we = sn;
                    }
                    2 => {
                        self.waypoint_sn = -sn;
                        self.waypoint_we = -we;
                    }
                    3 => {
                        self.waypoint_sn = we;
                        self.waypoint_we = -sn;
                    }
                    _ => panic!("can't handle"),
                }
            }
            Instruction::F(n) => {
                self.dist_sn += self.waypoint_sn * *n as isize;
                self.dist_we += self.waypoint_we * *n as isize;
            }
        }
    }
    fn execute(&mut self) {
        let code = &self.codes[self.ip].clone();
        // print!("{:?}\t", code);
        if self.mode == 1 {
            self.decode1(code);
        } else {
            self.decode2(code);
        }
        self.ip += 1;
    }
    fn stopped(&self) -> bool {
        self.codes.len() == self.ip
    }
}
