//! <https://adventofcode.com/2019/day/25>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        line_parser,
    },
    std::collections::{HashMap, VecDeque},
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
}

#[aoc(2019, 25)]
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
        let stdin = std::io::stdin();
        let mut buffer = String::new();
        let mut droid = Intcode::new(&self.line);
        let mut input: VecDeque<isize> = VecDeque::new();
        let mut output: VecDeque<isize> = VecDeque::new();
        loop {
            match droid.run(&mut input, &mut output) {
                State::None => {
                    let message = output.iter().map(|c| *c as u8 as char).collect::<String>();
                    print!("{message}");
                    buffer.clear();
                    output.clear();
                    return 0;
                }
                State::HasOutput => {}
                State::WaitInput => {
                    let message = output.iter().map(|c| *c as u8 as char).collect::<String>();
                    output.clear();
                    print!("{message}");
                    if message.is_empty() {
                        return 0;
                    }
                    buffer.clear();
                    stdin.read_line(&mut buffer).expect("fail to io");
                    for c in buffer.trim().chars() {
                        input.push_back(c as usize as isize);
                    }
                    input.push_back(b'\n' as usize as isize);
                }
            }
        }
    }
    fn part2(&mut self) -> Self::Output2 {
        0
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
enum State {
    #[default]
    None,
    WaitInput, // addr
    HasOutput, // value
}

#[derive(Debug, Default, Eq, PartialEq)]
struct Intcode {
    memory: HashMap<usize, isize>,
    pc: usize,
    r_base: usize,
    state: State,
}

impl Intcode {
    fn new(code: &[isize]) -> Self {
        let mut cpu: Intcode = Intcode::default();
        cpu.initialize(code);
        cpu
    }
    fn initialize(&mut self, code: &[isize]) {
        self.memory = HashMap::new();
        for (i, v) in code.iter().enumerate() {
            self.memory.insert(i, *v);
        }
        self.pc = 0;
        self.r_base = 0;
        self.state = State::None;
    }
    fn run(&mut self, inputs: &mut VecDeque<isize>, outputs: &mut VecDeque<isize>) -> State {
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
                        self.pc += 2;
                    } else {
                        return State::WaitInput;
                    }
                }
                4 => {
                    let op1 = deref!(1, true);
                    outputs.push_back(op1);
                    self.pc += 2;
                    return State::HasOutput;
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
        State::None
    }
}
