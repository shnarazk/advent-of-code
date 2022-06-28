//! <https://adventofcode.com/2019/day/7>
use crate::{
    framework::{aoc, AdventOfCode, ParseError},
    line_parser,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<isize>,
}

#[aoc(2019, 7)]
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
        let mut highest_score = 0;
        for init_a in 0..5 {
            let out_a = self.clone().execute(vec![init_a, 0]);
            for init_b in 0..5 {
                if init_b == init_a {
                    continue;
                }
                let out_b = self.clone().execute(vec![init_b, out_a[0]]);
                for init_c in 0..5 {
                    if init_c == init_b || init_c == init_a {
                        continue;
                    }
                    let out_c = self.clone().execute(vec![init_c, out_b[0]]);
                    for init_d in 0..5 {
                        if init_d == init_c || init_d == init_b || init_d == init_a {
                            continue;
                        }
                        let out_d = self.clone().execute(vec![init_d, out_c[0]]);
                        for init_e in 0..5 {
                            if init_e == init_d
                                || init_e == init_c
                                || init_e == init_b
                                || init_e == init_a
                            {
                                continue;
                            }
                            let out_e = self.clone().execute(vec![init_e, out_d[0]]);
                            if highest_score < out_e[0] {
                                println!("{},{},{},{},{}", init_a, init_b, init_c, init_d, init_e);
                                highest_score = out_e[0];
                            }
                        }
                    }
                }
            }
        }
        dbg!(highest_score) as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut amp = vec![
            self.clone(),
            self.clone(),
            self.clone(),
            self.clone(),
            self.clone(),
        ];
        let mut highest_score = 0;
        // for perm in permutations(0, 5) {
        //     todo!();
        // }
        dbg!(highest_score) as usize
    }
}

impl Puzzle {
    fn execute(&mut self, inputs: Vec<isize>) -> Vec<isize> {
        let memory = &mut self.line;
        let mut input_index = 0;
        let mut output: Vec<isize> = Vec::new();
        let mut pc = 0;
        loop {
            let op = memory[pc] % 100;
            let immediate: Vec<bool> = {
                let mut v = Vec::new();
                let mut val = memory[pc] / 100;
                while 0 < val {
                    v.push(0 < val % 10);
                    val /= 10;
                }
                v
            };
            macro_rules! fetch {
                ($offset: expr) => {{
                    if let Some(true) = immediate.get($offset - 1) {
                        memory[pc + $offset]
                    } else {
                        memory[memory[pc + $offset] as usize]
                    }
                }};
                ($offset: expr, true) => {{
                    memory[pc + $offset] as usize
                }};
            }
            match op {
                1 => {
                    let dst = fetch!(3, true);
                    memory[dst] = fetch!(1) + fetch!(2);
                    pc += 4;
                }
                2 => {
                    let dst = fetch!(3, true);
                    memory[dst] = fetch!(1) * fetch!(2);
                    pc += 4;
                }
                3 => {
                    let dst = fetch!(1, true);
                    memory[dst] = inputs[input_index];
                    input_index += 1;
                    pc += 2;
                }
                4 => {
                    let op1 = fetch!(1);
                    output.push(op1);
                    pc += 2;
                }
                5 => {
                    let op1 = fetch!(1);
                    let dst = fetch!(2) as usize;
                    if 0 != op1 {
                        pc = dst;
                    } else {
                        pc += 3;
                    }
                }
                6 => {
                    let op1 = fetch!(1);
                    let dst = fetch!(2) as usize;
                    if 0 == op1 {
                        pc = dst;
                    } else {
                        pc += 3;
                    }
                }
                7 => {
                    let op1 = fetch!(1);
                    let op2 = fetch!(2);
                    let dst = fetch!(3, true);
                    memory[dst] = (op1 < op2) as usize as isize;
                    pc += 4;
                }
                8 => {
                    let op1 = fetch!(1);
                    let op2 = fetch!(2);
                    let dst = fetch!(3, true);
                    memory[dst] = (op1 == op2) as usize as isize;
                    pc += 4;
                }
                99 => {
                    break;
                }
                _ => panic!("op: {op} at {pc}"),
            }
        }
        assert!(1 == output.len());
        output
    }
}
