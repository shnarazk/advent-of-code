//! <https://adventofcode.com/2019/day/13>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        line_parser,
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
    fn part1(&mut self) -> Self::Output1 {
        let mut env = Env::default();
        let verbose = !self.get_config().bench;
        if verbose {
            env.display(true);
        }
        self.start(&mut env);
        if verbose {
            env.display(false);
        }
        env.objects
            .iter()
            .filter(|(_, o)| **o == Object::Block)
            .count()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line[0] = 2;
        let verbose = !self.get_config().bench;
        let mut env = Env::default();
        if verbose {
            env.display(true);
        }
        self.start(&mut env);
        if verbose {
            env.display(false);
        }
        env.score
    }
}

impl Puzzle {
    fn start(&mut self, environment: &mut Env) {
        let verbose = !self.get_config().bench;
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
                    let i = environment.hanle_input(verbose);
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
#[derive(Clone, Debug, Default)]
pub struct Env {
    output_mode: usize,
    packet: [isize; 3],
    objects: HashMap<(isize, isize), Object>,
    score: usize,
    paddle_pos: isize,
    ball_pos: isize,
}

impl Env {
    pub fn hanle_input(&mut self, verbose: bool) -> isize {
        if verbose {
            self.display(false);
        }
        (self.ball_pos - self.paddle_pos).signum()
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
    fn display(&mut self, init: bool) {
        if !init {
            print!("\x1B[25A\x1B[1G");
        } else {
            println!();
        }
        for y in 0..24 {
            for x in 0..42 {
                if let Some(o) = self.objects.get(&(y, x)) {
                    let d = match o {
                        Object::Empty => " ",
                        Object::Wall => "#",
                        Object::Block => "*",
                        Object::Paddle => {
                            self.paddle_pos = x;
                            "T"
                        }
                        Object::Ball => {
                            self.ball_pos = x;
                            "o"
                        }
                    };
                    print!("{}", d);
                } else {
                    print!(" ");
                }
            }
            if y == 23 {
                println!(" SCORE: {}", self.score);
            } else {
                println!();
            }
        }
        // std::thread::sleep(std::time::Duration::from_millis(2));
    }
}
