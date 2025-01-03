//! <https://adventofcode.com/2019/day/17>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser,
    },
    std::{
        collections::{HashMap, VecDeque},
        ops::Add,
    },
};

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
enum Segment {
    L(usize),
    R(usize),
}

impl std::fmt::Debug for Segment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Segment::L(n) => write!(f, "L{}", n),
            Segment::R(n) => write!(f, "R{}", n),
        }
    }
}

fn decompose(original_v: &[Segment]) -> Option<Vec<Vec<Segment>>> {
    for start_len in 1..6 {
        let mut v: &[Segment] = original_v;
        let seg_beg = v[0..start_len].to_vec();
        let mut vv = Vec::new();
        let mut i = 0;
        while start_len <= v[i..].len() {
            if v[i..].starts_with(&seg_beg) {
                if 0 < i {
                    vv.push(&v[..i]);
                }
                v = &v[i + start_len..];
                i = 0;
            } else {
                i += 1;
            }
        }
        if !v.is_empty() {
            vv.push(v);
        }
        for end_len in 1..6.min(v.len()) {
            let seg_end = v[v.len() - end_len..v.len()].to_vec();
            let mut vvv = Vec::new();
            for pv in vv.iter() {
                let mut v = *pv;
                let mut i = 0;
                while end_len <= v[i..].len() {
                    if v[i..].starts_with(&seg_end) {
                        if 0 < i {
                            vvv.push(&v[..i]);
                        }
                        v = &v[i + end_len..];
                        i = 0;
                    } else {
                        i += 1;
                    }
                }
                if !v.is_empty() {
                    vvv.push(v);
                }
            }
            let mut seg_mid = vvv[0];
            for another in vvv.iter() {
                if another.len() < seg_mid.len() {
                    seg_mid = another;
                }
            }
            if seg_mid.len() <= 10
                && vvv
                    .iter()
                    .all(|v| v.iter().all(|seg| seg_mid.contains(seg)))
                && vvv.iter().all(|v| v[0] == seg_mid[0])
                && vvv.iter().all(|v| v[1] == seg_mid[1])
                && vvv.iter().all(|v| v.last() == seg_mid.last())
                && vvv
                    .iter()
                    .all(|v| v.len() != seg_mid.len() || **v == *seg_mid)
            {
                // println!("Whole path: {original_v:?}");
                // println!("Function A: {seg_beg:?}");
                // println!("Function B: {seg_mid:?}");
                // println!("Function C: {seg_end:?}");
                // println!("Some proof: {vvv:?}");
                return Some(vec![seg_beg, seg_mid.to_vec(), seg_end]);
            }
        }
    }
    None
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<isize>,
    memory: HashMap<usize, isize>,
    pc: usize,
    r_base: usize,
    cross_points: Vec<Location>,
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
        self.line = parser::to_isizes(block, &[','])?;
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let map: HashMap<Location, u8> = self.recognize();
        // for y in -1..46 {
        //     print!("|");
        //     for x in -2..39 {
        //         print!("{}", *map.get(&Location(y, x)).unwrap_or(&b'?') as char);
        //     }
        //     println!("|");
        // }
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
                self.cross_points.push(*loc);
                val += (loc.0 * loc.1) as usize;
            }
        }
        val
    }
    fn part2(&mut self) -> Self::Output2 {
        let map: HashMap<Location, u8> = self.recognize();
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
                self.cross_points.push(*loc);
            }
        }
        self.cross_points.sort();
        debug_assert_eq!(12, self.cross_points.len());
        let mut flow: Vec<u8> = Vec::new();
        let mut functions: Vec<Vec<Segment>> = Vec::new();
        // let mut best: Vec<Segment> = Vec::new();
        'found: for permutation in 0..3usize.pow(12_u32) {
            let mut location: Location = *map.iter().find(|(_, v)| **v == b'^').unwrap().0;
            let mut direction = Direction::North;
            let mut prev_location: Location = location;
            let mut trace: Vec<u8> = Vec::new();
            let mut last_action: u8 = 0;
            let mut debug_trace = std::collections::HashSet::new();
            let dir = |i: u32| permutation / 3_usize.pow(i) % 3_usize.pow(i + 1);
            while let Some(mut action) = seek(&map, location, direction, prev_location) {
                if let Some((i, _)) = self
                    .cross_points
                    .iter()
                    .enumerate()
                    .find(|(_, l)| **l == location)
                {
                    match dir(i as u32) {
                        1 => action = b'R',
                        2 => action = b'L',
                        _ => action = b'F',
                    }
                }
                let act = if action == last_action { b'F' } else { action };
                trace.push(act);
                debug_trace.insert(location);
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
            debug_trace.insert(location);
            if 259 == debug_trace.len() {
                let mut kinds = HashMap::new();
                let mut segments: Vec<Segment> = Vec::new();
                let mut clockwise = false;
                let mut steps = 0;
                for a in trace.iter() {
                    match *a {
                        b'F' => {
                            steps += 1;
                        }
                        b'R' | b'L' => {
                            if 0 < steps {
                                segments.push(if clockwise {
                                    Segment::R(steps)
                                } else {
                                    Segment::L(steps)
                                });
                                steps = 0;
                            }
                            clockwise = *a == b'R';
                        }
                        _ => unreachable!(),
                    }
                }
                segments.push(if clockwise {
                    Segment::R(steps)
                } else {
                    Segment::L(steps)
                });
                for seg in segments.iter() {
                    *kinds.entry(seg).or_insert(0) += 1;
                }
                if let Some(fs) = decompose(&segments) {
                    let mut seg: &[Segment] = &segments;
                    while !seg.is_empty() {
                        match () {
                            _ if seg.starts_with(&fs[0]) => {
                                flow.push(0);
                                seg = &seg[fs[0].len()..];
                            }
                            _ if seg.starts_with(&fs[1]) => {
                                flow.push(1);
                                seg = &seg[fs[1].len()..];
                            }
                            _ if seg.starts_with(&fs[2]) => {
                                flow.push(2);
                                seg = &seg[fs[2].len()..];
                            }
                            _ => (),
                        }
                    }
                    functions = fs;
                    // println!("Main func:  {:?}", &flow);
                    break 'found;
                }
            }
        }
        // build input!
        let mut inputs: VecDeque<isize> = VecDeque::new();
        for num in flow.iter() {
            inputs.push_back((b'A' + num) as isize);
            inputs.push_back(b',' as isize);
        }
        inputs.pop_back();
        inputs.push_back(b'\n' as isize);
        for v in functions.iter() {
            for seg in v.iter() {
                match seg {
                    Segment::L(n) => {
                        inputs.push_back(b'L' as isize);
                        inputs.push_back(b',' as isize);
                        if 9 < *n {
                            inputs.push_back((b'0' + (*n / 10) as u8) as isize);
                        }
                        inputs.push_back((b'0' + (*n % 10) as u8) as isize);
                        inputs.push_back(b',' as isize);
                    }
                    Segment::R(n) => {
                        inputs.push_back(b'R' as isize);
                        inputs.push_back(b',' as isize);
                        if 9 < *n {
                            inputs.push_back((b'0' + (*n / 10) as u8) as isize);
                        }
                        inputs.push_back((b'0' + (*n % 10) as u8) as isize);
                        inputs.push_back(b',' as isize);
                    }
                }
            }
            inputs.pop_back();
            inputs.push_back(b'\n' as isize);
        }
        inputs.push_back(b'n' as isize);
        inputs.push_back(b'\n' as isize);
        // println!("{:?}", inputs);
        // for c in inputs.iter() {
        //     print!("{}", *c as u8 as char);
        // }
        // println!();
        self.line[0] = 2;
        self.initialize();
        let mut total: usize = 0;
        while let Some(dusts) = self.run(&mut inputs) {
            total = dusts as usize;
        }
        total
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
        while let Some(o) = self.run(&mut VecDeque::new()) {
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
