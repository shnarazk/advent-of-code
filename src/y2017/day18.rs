//! <https://adventofcode.com/2017/day/18>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::{HashMap, VecDeque},
};

type Channel = [VecDeque<usize>; 2];

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Val {
    Reg(char),
    Lit(isize),
}

impl Val {
    fn is_lit(&self) -> bool {
        matches!(self, Val::Lit(_))
    }
    fn is_reg(&self) -> bool {
        !self.is_lit()
    }
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

impl TryFrom<&str> for Inst {
    type Error = ParseError;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        // dbg!(value);
        let arg1l = regex!(r"^([[:lower:]]{3}) (-?[[:digit:]]+)$");
        let arg1r = regex!(r"^([[:lower:]]{3}) ([[:lower:]])$");
        let arg2ll = regex!(r"^([[:lower:]]{3}) (-?[[:digit:]]+) (-?[[:digit:]]+)$");
        let arg2lr = regex!(r"^([[:lower:]]{3}) (-?[[:digit:]]+) ([[:lower:]])$");
        let arg2rl = regex!(r"^([[:lower:]]{3}) ([[:lower:]]) (-?[[:digit:]]+)$");
        let arg2rr = regex!(r"^([[:lower:]]{3}) ([[:lower:]]) ([[:lower:]])$");
        if let Some(segment) = arg1l.captures(value) {
            let val: Val = Val::Lit(segment[2].parse::<isize>()?);
            let ins = match &segment[1] {
                "snd" => Inst::Snd(val),
                "rcv" => Inst::Rcv(val),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        if let Some(segment) = arg1r.captures(value) {
            let reg: Val = Val::Reg(segment[2].chars().next().ok_or(ParseError)?);
            let ins = match &segment[1] {
                "snd" => Inst::Snd(reg),
                "rcv" => Inst::Rcv(reg),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        if let Some(segment) = arg2ll.captures(value) {
            let op1: Val = Val::Lit(segment[2].parse::<isize>()?);
            let op2: Val = Val::Lit(segment[3].parse::<isize>()?);
            let ins = match &segment[1] {
                "set" => Inst::Set(op1, op2),
                "add" => Inst::Add(op1, op2),
                "mul" => Inst::Mul(op1, op2),
                "mod" => Inst::Mod(op1, op2),
                "jgz" => Inst::Jgz(op1, op2),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        if let Some(segment) = arg2lr.captures(value) {
            let op1: Val = Val::Lit(segment[2].parse::<isize>()?);
            let op2: Val = Val::Reg(segment[3].chars().next().ok_or(ParseError)?);
            let ins = match &segment[1] {
                "set" => Inst::Set(op1, op2),
                "add" => Inst::Add(op1, op2),
                "mul" => Inst::Mul(op1, op2),
                "mod" => Inst::Mod(op1, op2),
                "jgz" => Inst::Jgz(op1, op2),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        if let Some(segment) = arg2rl.captures(value) {
            let op1: Val = Val::Reg(segment[2].chars().next().ok_or(ParseError)?);
            let op2: Val = Val::Lit(segment[3].parse::<isize>()?);
            let ins = match &segment[1] {
                "set" => Inst::Set(op1, op2),
                "add" => Inst::Add(op1, op2),
                "mul" => Inst::Mul(op1, op2),
                "mod" => Inst::Mod(op1, op2),
                "jgz" => Inst::Jgz(op1, op2),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        if let Some(segment) = arg2rr.captures(value) {
            let op1: Val = Val::Reg(segment[2].chars().next().ok_or(ParseError)?);
            let op2: Val = Val::Reg(segment[3].chars().next().ok_or(ParseError)?);
            let ins = match &segment[1] {
                "set" => Inst::Set(op1, op2),
                "add" => Inst::Add(op1, op2),
                "mul" => Inst::Mul(op1, op2),
                "mod" => Inst::Mod(op1, op2),
                "jgz" => Inst::Jgz(op1, op2),
                _ => unreachable!(),
            };
            return Ok(ins);
        }
        Err(ParseError)
    }
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
                    println!("send {:?}{} => {}", op1, x, self.pc + 1);
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
                        println!("id{} got {}", self.id, v);
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

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Inst>,
}

#[aoc(2017, 18)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line.push(Inst::try_from(block)?);
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
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
