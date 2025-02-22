//! <https://adventofcode.com/2019/day/11>

use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser,
    },
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
    pc: usize,
}

#[aoc(2019, 11)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = parser::to_isizes(input, &[','])?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut env = Env::default();
        self.start(&mut env);
        env.panel.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut env = Env::default();
        env.panel.insert((0, 0), (true, 0));
        self.start(&mut env);
        let y_beg = env.panel.keys().map(|loc| loc.0).min().unwrap();
        let y_end = env.panel.keys().map(|loc| loc.0).max().unwrap();
        let x_beg = env.panel.keys().map(|loc| loc.1).min().unwrap();
        let x_end = env.panel.keys().map(|loc| loc.1).max().unwrap();
        for y in y_beg..=y_end {
            for x in x_beg..=x_end {
                if env.panel.get(&(y, x)).is_some_and(|(c, _)| *c) {
                    print!("*");
                } else {
                    print!(" ");
                }
            }
            println!();
        }
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
            // println!("opcode {} at {}", op, pc);
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
                    // println!(
                    //     "read from {} then write-access: {}/mode: {:?}",
                    //     pc + $offset,
                    //     memory[&(pc + $offset)],
                    //     immediate.get($offset - 1)
                    // );
                    match immediate.get($offset - 1) {
                        Some(0) | None => memory[&(pc + $offset)] as usize,
                        Some(1) => (pc + $offset) as usize,
                        Some(2) => (r_base as isize + memory[&(pc + $offset)]) as usize,
                        _ => unreachable!(),
                    }
                }};
                ($offset: expr, true) => {{
                    // println!(
                    //     "read from {} then fetch: {}/mode: {:?}",
                    //     pc + $offset,
                    //     memory[&(pc + $offset)],
                    //     immediate.get($offset - 1)
                    // );
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

#[derive(Clone, Debug)]
pub struct Env {
    panel: HashMap<(isize, isize), (bool, usize)>,
    location: (isize, isize),
    direction: (isize, isize),
    output_even: bool,
}

impl Default for Env {
    fn default() -> Self {
        Env {
            panel: HashMap::new(),
            location: (0, 0),
            direction: (-1, 0),
            output_even: false,
        }
    }
}

impl Env {
    pub fn hanle_input(&mut self) -> isize {
        let input = if let Some(color) = self.panel.get(&self.location) {
            color.0 as usize as isize
        } else {
            0
        };
        input
    }
    pub fn hanle_output(&mut self, output: isize) {
        // dbg!(output);
        self.output_even = !self.output_even;
        if self.output_even {
            self.paint_at(output);
        } else {
            self.rotate(output);
        }
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
        // println!("({}, {})", self.location.0, self.location.1);
    }
}
