//! <https://adventofcode.com/2019/day/13>
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

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<isize>,
    pc: usize,
}

#[aoc(2019, 13)]
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
        let mut env = Env::default();
        self.start(&mut env);
        env.display();
        env.objects
            .iter()
            .filter(|(_, o)| **o == Object::Block)
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line[0] = 2;
        let mut env = Env::default();
        self.start(&mut env);
        env.display();
        0
    }
}

impl Puzzle {
    fn start(&mut self, environment: &mut Env) {
        let mut memory: HashMap<usize, isize> = HashMap::new();
        for (i, v) in self.line.iter().enumerate() {
            memory.insert(i, *v);
        }
        let mut pc: usize = 0;
        let mut r_base: usize = 0;
        loop {
            let op = memory[&pc] % 100;
            let immediate: Vec<u8> = {
                let mut v = Vec::new();
                let mut val = memory[&pc] / 100;
                while 0 < val {
                    v.push((val % 10) as u8);
                    val /= 10;
                }
                v
            };
            macro_rules! deref {
                ($offset: expr) => {{
                    match immediate.get($offset - 1) {
                        Some(0) | None => memory[&(pc + $offset)] as usize,
                        Some(1) => (pc + $offset) as usize,
                        Some(2) => (r_base as isize + memory[&(pc + $offset)]) as usize,
                        _ => unreachable!(),
                    }
                }};
                ($offset: expr, true) => {{
                    let addr: usize = match immediate.get($offset - 1) {
                        Some(0) | None => memory[&(pc + $offset)] as usize,
                        Some(1) => pc + $offset,
                        Some(2) => (r_base as isize + memory[&(pc + $offset)]) as usize,
                        _ => unreachable!(),
                    };
                    memory.get(&addr).map_or(0, |p| *p)
                }};
            }
            match op {
                1 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    memory.insert(dst, op1 + op2);
                    pc += 4;
                }
                2 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    memory.insert(dst, op1 * op2);
                    pc += 4;
                }
                3 => {
                    let dst = deref!(1);
                    let i = environment.hanle_input();
                    // println!("input at {pc}");
                    memory.insert(dst, i);
                    pc += 2;
                }
                4 => {
                    let op1 = deref!(1, true);
                    environment.hanle_output(op1);
                    pc += 2;
                }
                5 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    if 0 != op1 {
                        pc = op2 as usize;
                    } else {
                        pc += 3;
                    }
                }
                6 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    if 0 == op1 {
                        pc = op2 as usize;
                    } else {
                        pc += 3;
                    }
                }
                7 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    memory.insert(dst, (op1 < op2) as usize as isize);
                    pc += 4;
                }
                8 => {
                    let op1 = deref!(1, true);
                    let op2 = deref!(2, true);
                    let dst = deref!(3);
                    memory.insert(dst, (op1 == op2) as usize as isize);
                    pc += 4;
                }
                9 => {
                    let op1 = deref!(1, true);
                    r_base = (r_base as isize + op1) as usize;
                    pc += 2;
                }
                99 => {
                    break;
                }
                _ => panic!("op: {op} at {pc}"),
            }
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Object {
    Empty = 0,
    Wall,
    Block,
    Paddle,
    Ball,
}

impl TryFrom<usize> for Object {
    type Error = ();
    fn try_from(v: usize) -> Result<Self, Self::Error> {
        match v {
            0 => Ok(Object::Empty),
            1 => Ok(Object::Wall),
            2 => Ok(Object::Block),
            3 => Ok(Object::Paddle),
            4 => Ok(Object::Ball),
            _ => unreachable!(),
        }
    }
}
#[derive(Clone, Debug)]
pub struct Env {
    panel: HashMap<(isize, isize), (bool, usize)>,
    location: (isize, isize),
    direction: (isize, isize),
    output_mode: usize,
    packet: [isize; 3],
    objects: HashMap<(isize, isize), Object>,
    score: usize,
}

impl Default for Env {
    fn default() -> Self {
        Env {
            panel: HashMap::new(),
            location: (0, 0),
            direction: (-1, 0),
            output_mode: 0,
            packet: [0; 3],
            objects: HashMap::new(),
            score: 0,
        }
    }
}

impl Env {
    pub fn hanle_input(&mut self) -> isize {
        self.display();
        let input = if let Some(color) = self.panel.get(&self.location) {
            color.0 as usize as isize
        } else {
            0
        };
        input
    }
    pub fn hanle_output(&mut self, output: isize) {
        self.packet[self.output_mode] = output;
        if self.output_mode == 2 {
            if self.packet[0] == -1 && self.packet[1] == 0 {
                self.score = self.packet[2] as usize;
            } else {
                self.objects.insert(
                    (self.packet[1], self.packet[0]),
                    Object::try_from(self.packet[2] as usize).unwrap(),
                );
            }
        }
        self.output_mode = (self.output_mode + 1) % 3;
    }
    fn paint_at(&mut self, paint_white: isize) {
        let entry = self.panel.entry(self.location).or_insert((false, 0));
        *entry = (paint_white == 1, entry.1 + 1);
    }
    fn rotate(&mut self, turn_right: isize) {
        self.direction = match (self.direction, turn_right) {
            ((-1, 0), 0) => (0, -1),
            ((-1, 0), 1) => (0, 1),
            ((0, 1), 0) => (-1, 0),
            ((0, 1), 1) => (1, 0),
            ((1, 0), 0) => (0, 1),
            ((1, 0), 1) => (0, -1),
            ((0, -1), 0) => (1, 0),
            ((0, -1), 1) => (-1, 0),
            _ => unreachable!(),
        };
        self.location.0 += self.direction.0;
        self.location.1 += self.direction.1;
    }
    fn display(&self) {
        for y in 0..24 {
            for x in 0..70 {
                if let Some(o) = self.objects.get(&(y, x)) {
                    let d = match o {
                        Object::Empty => " ",
                        Object::Wall => "#",
                        Object::Block => "W",
                        Object::Paddle => "_",
                        Object::Ball => "O",
                    };
                    print!("{}", d);
                } else {
                    print!(" ");
                }
            }
            println!();
        }
    }
}
