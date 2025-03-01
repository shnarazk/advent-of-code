//! <https://adventofcode.com/2019/day/19>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        parser,
    },
    std::collections::{HashMap, VecDeque},
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<isize>,
    memory: HashMap<usize, isize>,
    pc: usize,
    r_base: usize,
}

#[aoc(2019, 19)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = parser::to_isizes(input, &[','])?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.initialize();
        let mut count: usize = 0;
        for y in 0..50 {
            for x in 0..50 {
                let on = self.is_pulling(y, x);
                count += on as usize;
                // print!("{}", if on { "#" } else { "." });
            }
            // println!();
        }
        count
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut border: HashMap<usize, usize> = HashMap::new();
        self.initialize();
        let mut y: usize = 1;
        let mut x: usize = 1;
        'first_on: for yy in 1..100 {
            for xx in 1..100 {
                if self.is_pulling(yy as isize, xx as isize) {
                    y = yy;
                    x = xx;
                    break 'first_on;
                }
            }
        }
        let mut span_x = 0;
        let mut span_y = 0;
        'not_enough_span: loop {
            x += span_x;
            'horizontal: loop {
                if self.is_pulling(y as isize, x as isize) {
                    x += 1;
                    span_x += 1;
                    continue 'horizontal;
                }
                x -= 1;
                break 'horizontal;
            }
            y += span_y;
            'vertical: loop {
                if self.is_pulling(y as isize, x as isize) {
                    y += 1;
                    span_y += 1;
                    continue 'vertical;
                }
                if 100 <= span_y && 100 <= span_x {
                    break 'not_enough_span;
                }
                y -= 1;
                break 'vertical;
            }
            // dbg!(span_y, span_x);
            if span_y == 1 && span_x == 1 {
                x += 1;
                y += 1;
            }
        }
        let start_y = y;
        let mut start_x: usize = x + span_x;
        'next_y: for y in start_y.. {
            let mut span = 0;
            for x in start_x.. {
                let on = self.is_pulling(y as isize, x as isize);
                if span == 0 && on {
                    if let Some(xx) = border.get(&(y - 99)) {
                        if x + 99 <= *xx {
                            return x * 10_000 + (y - 99);
                        }
                    }
                    span = 1;
                    start_x = x - 1;
                } else if 0 < span {
                    if on {
                        span += 1;
                    } else {
                        border.insert(y, x - 1);
                        continue 'next_y;
                    }
                }
            }
        }
        unreachable!()
        //count
    }
}

impl Puzzle {
    fn is_pulling(&mut self, y: isize, x: isize) -> bool {
        let mut input: VecDeque<isize> = VecDeque::new();
        assert!(0 <= x);
        input.push_back(x);
        assert!(0 <= y);
        input.push_back(y);
        self.initialize(); // required
        if let Some(flag) = self.run(&mut input) {
            return flag == 1;
        }
        panic!();
    }
    fn initialize(&mut self) {
        self.memory = HashMap::new();
        for (i, v) in self.line.iter().enumerate() {
            self.memory.insert(i, *v);
        }
        self.pc = 0;
        self.r_base = 0;
    }
    fn run(&mut self, inputs: &mut VecDeque<isize>) -> Option<isize> {
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
                    if let Some(i) = inputs.pop_front() {
                        self.memory.insert(dst, i);
                    } else {
                        panic!("No more input.");
                    }
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
