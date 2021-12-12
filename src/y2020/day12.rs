use {
    crate::y2020::traits::{Description, ProblemObject, ProblemSolver},
    lazy_static::lazy_static,
    regex::Regex,
};

pub fn day12(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

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

impl ProblemObject for Instruction {
    fn parse(s: &str) -> Option<Self> {
        Instruction::from(s)
    }
}

impl Instruction {
    fn from(str: &str) -> Option<Self> {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"^(N|S|E|W|L|R|F)(\d+)$").expect("bad");
        }
        if let Some(m) = RE.captures(str) {
            if let Ok(n) = &m[2].parse::<usize>() {
                match &m[1] {
                    "N" => Some(Instruction::N(*n)),
                    "S" => Some(Instruction::S(*n)),
                    "E" => Some(Instruction::E(*n)),
                    "W" => Some(Instruction::W(*n)),
                    "L" => Some(Instruction::L(*n)),
                    "R" => Some(Instruction::R(*n)),
                    "F" => Some(Instruction::F(*n)),
                    _ => None,
                }
            } else {
                // panic!("mnemonic.{}, sign.{}, val.{}", &m[1], &m[2], &m[3]);
                None
            }
        } else {
            None
        }
    }
}

#[derive(Debug, PartialEq)]
struct Setting {
    codes: Vec<Instruction>,
    dir: Dir,
    waypoint_sn: isize,
    waypoint_we: isize,
    dist_sn: isize,
    dist_we: isize,
    ip: usize,
    mode: usize,
}

impl ProblemSolver<Instruction, usize, usize> for Setting {
    const YEAR: usize = 2020;
    const DAY: usize = 12;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Setting {
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
    fn insert(&mut self, inst: Instruction) {
        self.codes.push(inst);
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

impl Setting {
    fn distance(&self) -> usize {
        (self.dist_sn.abs() as usize) + (self.dist_we.abs() as usize)
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

#[cfg(feature = "y2020")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::y2020::traits::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        assert_eq!(
            Setting::parse(Description::FileTag("test".to_string())).run(1),
            Answer::Part1(25)
        );
    }
    #[test]
    fn test_part2() {
        assert_eq!(
            Setting::parse(Description::FileTag("test".to_string())).run(2),
            Answer::Part2(286)
        );
    }
}
