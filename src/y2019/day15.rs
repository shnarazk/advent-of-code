//! <https://adventofcode.com/2019/day/15>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser,
    },
    std::{
        cmp::Reverse,
        collections::{BinaryHeap, HashMap, HashSet},
        ops::Add,
    },
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
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
    Target,
    Wall,
    // Unknown,
}

impl From<isize> for Cell {
    fn from(v: isize) -> Self {
        match v {
            0 => Cell::Wall,
            1 => Cell::Empty,
            2 => Cell::Target,
            _ => unreachable!(),
        }
    }
}

#[aoc(2019, 15)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = parser::to_isizes(input, &[','])?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut map: HashMap<Location, Cell> = HashMap::new();
        let mut target = Location(0, 0);
        let mut location = Location(0, 0);
        let mut direction = Direction::North;
        map.insert(location, Cell::Empty);
        let mut output: Cell = Cell::default();
        self.initialize();
        let mut count = 0;
        while output != Cell::Target {
            output = Cell::from(self.run(direction.encode()));
            // println!(
            //     "Try {:?} @ ({}, {}) got {:?}",
            //     direction, location.0, location.1, output
            // );
            match output {
                Cell::Empty => {
                    location = location + direction.as_location();
                    map.insert(location, output);
                    direction = direction.rotate_backward();
                }
                Cell::Target => {
                    location = location + direction.as_location();
                    target = location;
                    map.insert(location, output);
                    direction = direction.rotate_backward();
                }
                Cell::Wall => {
                    let loc = location + direction.as_location();
                    map.insert(loc, output);
                    direction = direction.rotate_forward();
                }
            }
            // {
            //     print!("\x1B[45A\x1B[1G");
            //     for y in -25..20 {
            //         for x in -40..50 {
            //             print!(
            //                 "{}",
            //                 match map.get(&Location(y, x)).unwrap_or(&Cell::Unknown) {
            //                     Cell::Empty => " ",
            //                     Cell::Target => "!",
            //                     Cell::Wall => "#",
            //                     Cell::Unknown => "?",
            //                 }
            //             );
            //         }
            //         println!();
            //     }
            // }
        }
        while location != Location(0, 0) && count < 5000 {
            count += 1;
            output = Cell::from(self.run(direction.encode()));
            // println!(
            //     "Try {:?} @ ({}, {}) got {:?}",
            //     direction, location.0, location.1, output
            // );
            match output {
                Cell::Empty => {
                    location = location + direction.as_location();
                    map.insert(location, output);
                    direction = direction.rotate_backward();
                }
                Cell::Target => {
                    location = location + direction.as_location();
                    map.insert(location, output);
                    direction = direction.rotate_backward();
                }
                Cell::Wall => {
                    let loc = location + direction.as_location();
                    map.insert(loc, output);
                    direction = direction.rotate_forward();
                }
            }
            // {
            //     print!("\x1B[45A\x1B[1G");
            //     for y in -25..20 {
            //         for x in -40..50 {
            //             print!(
            //                 "{}",
            //                 match map.get(&Location(y, x)).unwrap_or(&Cell::Unknown) {
            //                     Cell::Empty => " ",
            //                     Cell::Target => "!",
            //                     Cell::Wall => "#",
            //                     Cell::Unknown => "?",
            //                 }
            //             );
            //         }
            //         println!();
            //     }
            // }
        }
        let mut to_visit: BinaryHeap<Reverse<(usize, Location)>> = BinaryHeap::new();
        let mut visited: HashSet<Location> = HashSet::new();
        to_visit.push(Reverse((0, Location(0, 0))));
        while let Some(Reverse((cost, pos))) = to_visit.pop() {
            if pos == target {
                return cost;
            }
            for p in pos
                .neighbors()
                .iter()
                .filter(|l| map.get(l) != Some(&Cell::Wall) && !visited.contains(l))
            {
                to_visit.push(Reverse((cost + 1, *p)));
            }
            visited.insert(pos);
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut map: HashMap<Location, Cell> = HashMap::new();
        let mut target = Location(0, 0);
        let mut location = Location(0, 0);
        let mut direction = Direction::North;
        map.insert(location, Cell::Empty);
        let mut output: Cell = Cell::default();
        self.initialize();
        let mut count = 0;
        while output != Cell::Target {
            output = Cell::from(self.run(direction.encode()));
            match output {
                Cell::Empty => {
                    location = location + direction.as_location();
                    map.insert(location, output);
                    direction = direction.rotate_backward();
                }
                Cell::Target => {
                    location = location + direction.as_location();
                    target = location;
                    map.insert(location, output);
                    direction = direction.rotate_backward();
                }
                Cell::Wall => {
                    let loc = location + direction.as_location();
                    map.insert(loc, output);
                    direction = direction.rotate_forward();
                }
            }
            // {
            //     print!("\x1B[45A\x1B[1G");
            //     for y in -25..20 {
            //         for x in -40..50 {
            //             print!(
            //                 "{}",
            //                 match map.get(&Location(y, x)).unwrap_or(&Cell::Unknown) {
            //                     Cell::Empty => " ",
            //                     Cell::Target => "!",
            //                     Cell::Wall => "#",
            //                     Cell::Unknown => "?",
            //                 }
            //             );
            //         }
            //         println!();
            //     }
            // }
        }
        while location != Location(0, 0) && count < 5000 {
            count += 1;
            output = Cell::from(self.run(direction.encode()));
            match output {
                Cell::Empty => {
                    location = location + direction.as_location();
                    map.insert(location, output);
                    direction = direction.rotate_backward();
                }
                Cell::Target => {
                    location = location + direction.as_location();
                    map.insert(location, output);
                    direction = direction.rotate_backward();
                }
                Cell::Wall => {
                    let loc = location + direction.as_location();
                    map.insert(loc, output);
                    direction = direction.rotate_forward();
                }
            }
            // {
            //     print!("\x1B[45A\x1B[1G");
            //     for y in -25..20 {
            //         for x in -40..50 {
            //             print!(
            //                 "{}",
            //                 match map.get(&Location(y, x)).unwrap_or(&Cell::Unknown) {
            //                     Cell::Empty => " ",
            //                     Cell::Target => "!",
            //                     Cell::Wall => "#",
            //                     Cell::Unknown => "?",
            //                 }
            //             );
            //         }
            //         println!();
            //     }
            // }
        }
        let mut max_cost = 0;
        let mut to_visit: BinaryHeap<Reverse<(usize, Location)>> = BinaryHeap::new();
        let mut visited: HashSet<Location> = HashSet::new();
        visited.insert(target);
        to_visit.push(Reverse((0, target)));
        while let Some(Reverse((cost, pos))) = to_visit.pop() {
            for p in pos
                .neighbors()
                .iter()
                .filter(|l| map.get(l) == Some(&Cell::Empty) && !visited.contains(l))
            {
                to_visit.push(Reverse((cost + 1, *p)));
                max_cost = max_cost.max(cost + 1);
            }
            visited.insert(pos);
            // {
            //     print!("\x1B[42A\x1B[1G");
            //     for y in -22..20 {
            //         for x in -40..50 {
            //             print!(
            //                 "{}",
            //                 match map.get(&Location(y, x)).unwrap_or(&Cell::Unknown) {
            //                     Cell::Empty if visited.contains(&Location(y, x)) => "O",
            //                     Cell::Empty => " ",
            //                     Cell::Target => "!",
            //                     Cell::Wall => "#",
            //                     Cell::Unknown => "?",
            //                 }
            //             );
            //         }
            //         println!();
            //     }
            // }
        }
        max_cost
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
