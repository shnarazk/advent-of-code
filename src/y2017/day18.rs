//! <https://adventofcode.com/2017/day/18>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::{HashMap, VecDeque},
};

type Channel = [VecDeque<usize>; 2];

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Val {
    Reg(char),
    Lit(isize),
}

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Inst {
    Snd(Val),
    Set(Val, Val),
    Add(Val, Val),
    Mul(Val, Val),
    Mod(Val, Val),
    Rcv(Val),
    Jgz(Val, Val),
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum RuntimeState {
    #[default]
    None,
    Receiving(usize),
    Sending(usize, usize),
}

#[derive(Debug, Default, Eq, PartialEq)]
struct Runtime {
    id: usize,
    pc: usize,
    register: HashMap<Val, isize>,
    memory: HashMap<usize, Inst>,
    frequency: usize,
    state: RuntimeState,
}

impl Runtime {
    fn initialize(iid: isize, code: &[Inst]) -> Runtime {
        let mut memory: HashMap<usize, Inst> = HashMap::new();
        for (addr, inst) in code.iter().enumerate() {
            memory.insert(addr, *inst);
        }
        let mut register: HashMap<Val, isize> = HashMap::new();
        if 0 <= iid {
            register.insert(Val::Reg('p'), iid);
        }
        Runtime {
            id: iid as usize,
            pc: 0,
            register,
            memory,
            frequency: 0,
            state: RuntimeState::None,
        }
    }
    fn get(&self, val: &Val) -> isize {
        match val {
            Val::Lit(n) => *n,
            _ => *self.register.get(val).unwrap_or(&0),
        }
    }
    fn set(&mut self, reg: &Val, val: isize) {
        self.register.insert(*reg, val);
    }
    fn execute(&mut self) -> Option<usize> {
        if let Some(inst) = self.memory.get(&self.pc) {
            let ins = *inst;
            // println!("{:>3} {:?}", self.pc, ins);
            match ins {
                Inst::Snd(op1) => {
                    let x = self.get(&op1);
                    self.frequency = x as usize;
                }
                Inst::Set(op1, op2) => {
                    let y = self.get(&op2);
                    self.set(&op1, y);
                }
                Inst::Add(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    self.set(&op1, x + y);
                }
                Inst::Mul(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    self.set(&op1, x * y);
                }
                Inst::Mod(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    assert!(0 != y);
                    self.set(&op1, x % y);
                }
                Inst::Rcv(op1) => {
                    let x = self.get(&op1);
                    if x != 0 {
                        return Some(self.frequency);
                    }
                }
                Inst::Jgz(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    if 0 < x {
                        let n: isize = self.pc as isize + y - 1;
                        assert!(0 <= n);
                        self.pc = n as usize;
                    }
                }
            };
            self.pc += 1;
        }
        None
    }
    fn execute2(&mut self, channel: &mut Channel) -> RuntimeState {
        let pc: usize = match self.state {
            RuntimeState::None => self.pc,
            RuntimeState::Receiving(addr) => addr,
            RuntimeState::Sending(addr, _) => addr,
        };
        self.state = RuntimeState::None;
        self.pc = pc;
        if let Some(inst) = self.memory.get(&self.pc) {
            let ins = *inst;
            // println!("{:>3} {:?}", self.pc, ins);
            match ins {
                Inst::Snd(op1) => {
                    let x = self.get(&op1);
                    self.frequency = x as usize;
                    self.state = RuntimeState::Sending(self.pc + 1, self.frequency);
                    // println!("send {:?}{} => {}", op1, x, self.pc + 1);
                    return self.state;
                }
                Inst::Set(op1, op2) => {
                    let y = self.get(&op2);
                    self.set(&op1, y);
                }
                Inst::Add(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    self.set(&op1, x + y);
                }
                Inst::Mul(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    self.set(&op1, x * y);
                }
                Inst::Mod(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    assert!(0 != y);
                    self.set(&op1, x % y);
                }
                Inst::Rcv(op1) => {
                    if let Some(v) = channel[self.id].pop_front() {
                        // println!("id{} got {}", self.id, v);
                        self.set(&op1, v as isize);
                    } else {
                        self.state = RuntimeState::Receiving(self.pc);
                        return self.state;
                    }
                }
                Inst::Jgz(op1, op2) => {
                    let x = self.get(&op1);
                    let y = self.get(&op2);
                    if 0 < x {
                        let n: isize = self.pc as isize + y - 1;
                        assert!(0 <= n);
                        self.pc = n as usize;
                    }
                }
            };
            self.pc += 1;
        }
        RuntimeState::None
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Inst>,
}

mod parser {
    use {
        super::*,
        crate::parser::parse_isize,
        winnow::{
            ascii::{newline, space1},
            combinator::{alt, separated, seq},
            token::one_of,
            ModalResult, Parser,
        },
    };

    fn parse_val(s: &mut &str) -> ModalResult<Val> {
        alt((
            parse_isize.map(Val::Lit),
            one_of(|c: char| c.is_ascii_lowercase()).map(Val::Reg),
        ))
        .parse_next(s)
    }

    fn parse_inst(s: &mut &str) -> ModalResult<Inst> {
        alt((
            seq!(_: "snd ", parse_val).map(|(a,)| Inst::Snd(a)),
            seq!(_: "set ", parse_val, _: space1, parse_val).map(|(a, b)| Inst::Set(a, b)),
            seq!(_: "add ", parse_val, _: space1, parse_val).map(|(a, b)| Inst::Add(a, b)),
            seq!(_: "mul ", parse_val, _: space1, parse_val).map(|(a, b)| Inst::Mul(a, b)),
            seq!(_: "mod ", parse_val, _: space1, parse_val).map(|(a, b)| Inst::Mod(a, b)),
            seq!(_: "rcv ", parse_val).map(|(a,)| Inst::Rcv(a)),
            seq!(_: "jgz ", parse_val, _: space1, parse_val).map(|(a, b)| Inst::Jgz(a, b)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Inst>> {
        separated(1.., parse_inst, newline).parse_next(s)
    }
}

#[aoc(2017, 18)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parser::parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut processor: Runtime = Runtime::initialize(-1, &self.line);
        loop {
            if let Some(f) = processor.execute() {
                return f;
            }
        }
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut processor0: Runtime = Runtime::initialize(0, &self.line);
        let mut processor1: Runtime = Runtime::initialize(1, &self.line);
        let mut channel: Channel = [VecDeque::new(), VecDeque::new()];
        let mut count: usize = 0;
        loop {
            match (
                processor0.execute2(&mut channel),
                processor1.execute2(&mut channel),
            ) {
                (RuntimeState::Receiving(_), RuntimeState::Receiving(_)) => {
                    return count;
                }
                (RuntimeState::Sending(_, p0), RuntimeState::Sending(_, p1)) => {
                    channel[1].push_back(p0);
                    channel[0].push_back(p1);
                    count += 1;
                }
                (RuntimeState::Sending(_, p0), _) => {
                    channel[1].push_back(p0);
                }
                (_, RuntimeState::Sending(_, p1)) => {
                    channel[0].push_back(p1);
                    count += 1;
                }
                (RuntimeState::None, _) | (_, RuntimeState::None) => (),
            }
        }
    }
}
