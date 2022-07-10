//! <https://adventofcode.com/2019/day/17>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        line_parser,
    },
    std::{
        collections::{HashMap, VecDeque},
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
    fn rotate_clockwise(&self) -> Self {
        match self {
            Direction::North => Direction::East,
            Direction::East => Direction::South,
            Direction::South => Direction::West,
            Direction::West => Direction::North,
        }
    }
    fn rotate_counterclockwise(&self) -> Self {
        match self {
            Direction::North => Direction::West,
            Direction::East => Direction::North,
            Direction::South => Direction::East,
            Direction::West => Direction::South,
        }
    }
    // fn encode(&self) -> isize {
    //     match self {
    //         Direction::North => 1,
    //         Direction::East => 4,
    //         Direction::South => 2,
    //         Direction::West => 3,
    //     }
    // }
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
        let map: HashMap<Location, u8> = self.recognize();
        for y in -1..46 {
            print!("|");
            for x in -2..39 {
                print!("{}", *map.get(&Location(y, x)).unwrap_or(&b' ') as char);
            }
            println!("|");
        }
        let mut count: usize = 0;
        let mut val: usize = 0;
        for (loc, cell) in map.iter() {
            if *cell != b'#' {
                continue;
            }
            if 2 < loc
                .neighbors()
                .iter()
                .filter(|l| map.get(l) == Some(&b'#'))
                .count()
            {
                count += 1;
                val += (loc.0 * loc.1) as usize;
            }
        }
        dbg!(count);
        val
    }
    fn part2(&mut self) -> Self::Output2 {
        let map: HashMap<Location, u8> = self.recognize();
        let mut location: Location = *map.iter().find(|(_, v)| **v == b'^').unwrap().0;
        let mut direction = Direction::North;
        let mut prev_location: Location = location;
        let mut trace: Vec<u8> = Vec::new();
        let mut last_action: u8 = 0;
        while let Some(action) = seek(&map, location, direction, prev_location) {
            let act = if action == last_action { b'F' } else { action };
            trace.push(act);
            match act {
                b'F' => {
                    prev_location = location;
                    location = location + direction.as_location();
                }
                b'L' => {
                    direction = direction.rotate_counterclockwise();
                }
                b'R' => {
                    direction = direction.rotate_clockwise();
                }
                _ => unreachable!(),
            }
            last_action = act;
        }
        dbg!(&location);
        for c in trace.iter() {
            print!("{}", *c as char);
        }
        println!();
        self.line[0] = 2;
        self.initialize();
        map.len()
    }
}

fn seek(
    map: &HashMap<Location, u8>,
    loc: Location,
    dir: Direction,
    prev_loc: Location,
) -> Option<u8> {
    // Firstly try to go forward.
    if map.get(&(loc + dir.as_location())) == Some(&b'#') {
        return Some(b'F');
    }
    // then seek the right direcotion.
    for next in loc.neighbors() {
        if next != prev_loc && map.get(&next) == Some(&b'#') {
            if next == loc + dir.rotate_clockwise().as_location() {
                return Some(b'R');
            }
            if next == loc + dir.rotate_counterclockwise().as_location() {
                return Some(b'L');
            }
            if next == loc + dir.as_location() {
                unreachable!();
            }
        }
    }
    None
}

impl Puzzle {
    fn recognize(&mut self) -> HashMap<Location, u8> {
        let mut map: HashMap<Location, u8> = HashMap::new();
        let mut output: VecDeque<u8> = VecDeque::new();
        self.initialize();
        while let Some(o) = self.run(None) {
            output.push_back(o as u8);
        }
        let mut y = 0;
        let mut x = 0;
        while let Some(cell) = output.pop_front() {
            if cell == b'\n' {
                y += 1;
                x = 0;
                continue;
            }
            map.insert(Location(y, x), cell);
            x += 1;
        }
        for y in -1..46 {
            print!("|");
            for x in -2..39 {
                print!("{}", *map.get(&Location(y, x)).unwrap_or(&b' ') as char);
            }
            println!("|");
        }
        map
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
    fn run(&mut self, mut input: Option<isize>) -> Option<isize> {
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
                    self.memory.insert(dst, input.expect("empty input"));
                    input = None;
                    self.pc += 2;
                }
                4 => {
                    let op1 = deref!(1, true);
                    self.pc += 2;
                    return Some(op1);
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
        None
    }
}
