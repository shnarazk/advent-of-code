//! <https://adventofcode.com/2019/day/23>
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
}

#[aoc(2019, 23)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: &str) -> Result<(), ParseError> {
        self.line = parser::to_isizes(input, &[','])?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut nodes: Vec<Intcode> = (0..50).map(|_| Intcode::default()).collect::<Vec<_>>();
        for node in nodes.iter_mut() {
            node.initialize(&self.line);
        }
        let mut network: HashMap<usize, (VecDeque<isize>, VecDeque<isize>)> = HashMap::new();
        for i in 0..50 {
            network
                .entry(i)
                .or_insert((VecDeque::new(), VecDeque::new()))
                .0
                .push_back(i as isize);
        }
        for _ in 0.. {
            for node in nodes.iter_mut() {
                node.run();
            }
            for (i, node) in nodes.iter().enumerate() {
                if let State::HasOutput(v) = node.state() {
                    let output_queue = &mut network.get_mut(&i).unwrap().1;
                    output_queue.push_back(*v);
                    if 2 < output_queue.len() {
                        let dist = output_queue.pop_front().unwrap() as usize;
                        let x = output_queue.pop_front().unwrap();
                        let y = output_queue.pop_front().unwrap();
                        if dist == 255 {
                            return y as usize;
                        }
                        let input_queue = &mut network.get_mut(&dist).unwrap().0;
                        input_queue.push_back(x);
                        input_queue.push_back(y);
                    }
                }
            }
            for (i, node) in nodes.iter_mut().enumerate() {
                if let State::WaitInput(_v) = node.state() {
                    let value = network.get_mut(&i).unwrap().0.pop_front().unwrap_or(-1);
                    node.resume_in(value);
                }
            }
        }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut last_y: isize = -4;
        let mut nodes: Vec<Intcode> = (0..50).map(|_| Intcode::default()).collect::<Vec<_>>();
        for node in nodes.iter_mut() {
            node.initialize(&self.line);
        }
        let mut network: HashMap<usize, (VecDeque<isize>, VecDeque<isize>)> = HashMap::new();
        for i in 0..50 {
            network
                .entry(i)
                .or_insert((VecDeque::new(), VecDeque::new()))
                .0
                .push_back(i as isize);
        }
        let mut nat: Nat = Nat::default();
        for _ in 0.. {
            for node in nodes.iter_mut() {
                node.run();
            }
            for (i, node) in nodes.iter().enumerate() {
                if let State::HasOutput(v) = node.state() {
                    let output_queue = &mut network.get_mut(&i).unwrap().1;
                    output_queue.push_back(*v);
                    if 2 < output_queue.len() {
                        let dist = output_queue.pop_front().unwrap() as usize;
                        let x = output_queue.pop_front().unwrap();
                        let y = output_queue.pop_front().unwrap();
                        if dist == 255 {
                            nat.receive(x, y);
                        } else {
                            let input_queue = &mut network.get_mut(&dist).unwrap().0;
                            input_queue.push_back(x);
                            input_queue.push_back(y);
                        }
                    }
                }
            }
            if let Some((x, y)) = nat.monitor_network_is_idle(&nodes, &network) {
                if y == last_y {
                    return y as usize;
                }
                last_y = y;
                let input_queue = &mut network.get_mut(&0).unwrap().0;
                input_queue.push_back(x);
                input_queue.push_back(y);
            }
            for (i, node) in nodes.iter_mut().enumerate() {
                if let State::WaitInput(_) = node.state() {
                    let value = network.get_mut(&i).unwrap().0.pop_front().unwrap_or(-1);
                    node.resume_in(value);
                }
            }
        }
        0
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
struct Nat {
    x: isize,
    y: isize,
    idling: usize,
}

impl Nat {
    fn receive(&mut self, x: isize, y: isize) {
        self.x = x;
        self.y = y;
    }
    fn monitor_network_is_idle(
        &mut self,
        nodes: &[Intcode],
        network: &HashMap<usize, (VecDeque<isize>, VecDeque<isize>)>,
    ) -> Option<(isize, isize)> {
        let cond = network.values().all(|(in_q, _out_q)| in_q.is_empty())
            && nodes
                .iter()
                .all(|n| matches!(n.state(), State::WaitInput(_)));
        if cond {
            self.idling += 1;
        } else {
            self.idling = 0;
        }
        (2 < self.idling).then_some((self.x, self.y))
    }
}

#[derive(Debug, Default, Eq, PartialEq)]
enum State {
    #[default]
    None,
    WaitInput(usize), // addr
    HasOutput(isize), // value
}

#[derive(Debug, Default, Eq, PartialEq)]
struct Intcode {
    memory: HashMap<usize, isize>,
    pc: usize,
    r_base: usize,
    state: State,
}

impl Intcode {
    fn state(&self) -> &State {
        &self.state
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
    fn resume_in(&mut self, val: isize) {
        if let State::WaitInput(addr) = self.state {
            self.memory.insert(addr, val);
            self.pc += 2;
        }
    }
    fn run(&mut self) -> &State {
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
                    self.state = State::WaitInput(dst);
                    return &self.state;
                }
                4 => {
                    let op1 = deref!(1, true);
                    self.pc += 2;
                    self.state = State::HasOutput(op1);
                    return &self.state;
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
        &State::None
    }
}
