//! <https://adventofcode.com/2019/day/17>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        line_parser,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, HashSet},
        ops::Add,
    },
};

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<isize>,
    memory: HashMap<usize, isize>,
    pc: usize,
    r_base: usize,
}

#[derive(Copy, Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Location(isize, isize);

impl Location {
    fn neighbors(&self) -> Vec<Location> {
        [
            Direction::North,
            Direction::East,
            Direction::South,
            Direction::West,
        ]
        .iter()
        .map(|d| *self + d.as_location())
        .collect::<Vec<_>>()
    }
}

#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq)]
enum Direction {
    #[default]
    North,
    East,
    South,
    West,
}
impl Direction {
    fn rotate_forward(&self) -> Self {
        match self {
            Direction::North => Direction::East,
            Direction::East => Direction::South,
            Direction::South => Direction::West,
            Direction::West => Direction::North,
        }
    }
    fn rotate_backward(&self) -> Self {
        match self {
            Direction::North => Direction::West,
            Direction::East => Direction::North,
            Direction::South => Direction::East,
            Direction::West => Direction::South,
        }
    }
    fn encode(&self) -> isize {
        match self {
            Direction::North => 1,
            Direction::East => 4,
            Direction::South => 2,
            Direction::West => 3,
        }
    }
    fn as_location(&self) -> Location {
        match self {
            Direction::North => Location(-1, 0),
            Direction::East => Location(0, 1),
            Direction::South => Location(1, 0),
            Direction::West => Location(0, -1),
        }
    }
}

impl Add for Location {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0, self.1 + other.1)
    }
}

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
enum Cell {
    #[default]
    Empty,
    Newline,
    Wall,
    RobotUp,
    RobotDown,
    RobotLeft,
    RobotRight,
    RobotOutOfControl,
}

impl From<isize> for Cell {
    fn from(v: isize) -> Self {
        match v as u8 {
            35 => Cell::Wall,
            46 => Cell::Empty,
            b'^' => Cell::RobotUp,
            b'v' => Cell::RobotDown,
            b'<' => Cell::RobotLeft,
            b'>' => Cell::RobotRight,
            b'X' => Cell::RobotOutOfControl,
            10 => Cell::Newline,
            _ => unreachable!(),
        }
    }
}

#[aoc(2019, 17)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = line_parser::to_isizes(block, ',')?;
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        // let mut map: HashMap<Location, Cell> = HashMap::new();
        // let mut output: Cell = Cell::default();
        self.initialize();
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

impl Puzzle {
    fn initialize(&mut self) {
        self.memory = HashMap::new();
        for (i, v) in self.line.iter().enumerate() {
            self.memory.insert(i, *v);
        }
        self.pc = 0;
        self.r_base = 0;
    }
    fn run(&mut self, input: isize) -> isize {
        loop {
            let op = self.memory[&self.pc] % 100;
            let immediate: Vec<u8> = {
                let mut v = Vec::new();
                let mut val = self.memory[&self.pc] / 100;
                while 0 < val {
                    v.push((val % 10) as u8);
                    val /= 10;
                }
                v
            };
            macro_rules! deref {
                ($offset: expr) => {{
                    match immediate.get($offset - 1) {
                        Some(0) | None => self.memory[&(self.pc + $offset)] as usize,
                        Some(1) => (self.pc + $offset) as usize,
                        Some(2) => {
                            (self.r_base as isize + self.memory[&(self.pc + $offset)]) as usize
                        }
                        _ => unreachable!(),
                    }
                }};
                ($offset: expr, true) => {{
                    let addr: usize = match immediate.get($offset - 1) {
                        Some(0) | None => self.memory[&(self.pc + $offset)] as usize,
                        Some(1) => self.pc + $offset,
                        Some(2) => {
                            (self.r_base as isize + self.memory[&(self.pc + $offset)]) as usize
                        }
                        _ => unreachable!(),
                    };
                    self.memory.get(&addr).map_or(0, |p| *p)
                }};
            }
            match op {
                1 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    self.memory.insert(dst, op1 + op2);
                    self.pc += 4;
                }
                2 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    self.memory.insert(dst, op1 * op2);
                    self.pc += 4;
                }
                3 => {
                    let dst = deref!(1);
                    // println!("input at {self.pc}");
                    self.memory.insert(dst, input);
                    self.pc += 2;
                }
                4 => {
                    let op1 = deref!(1, true);
                    self.pc += 2;
                    return op1;
                }
                5 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    if 0 != op1 {
                        self.pc = op2 as usize;
                    } else {
                        self.pc += 3;
                    }
                }
                6 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    if 0 == op1 {
                        self.pc = op2 as usize;
                    } else {
                        self.pc += 3;
                    }
                }
                7 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    self.memory.insert(dst, (op1 < op2) as usize as isize);
                    self.pc += 4;
                }
                8 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    self.memory.insert(dst, (op1 == op2) as usize as isize);
                    self.pc += 4;
                }
                9 => {
                    let op1 = deref!(1, true);
                    self.r_base = (self.r_base as isize + op1) as usize;
                    self.pc += 2;
                }
                99 => {
                    break;
                }
                _ => panic!("op: {op} at {}", self.pc),
            }
        }
        -1
    }
}
