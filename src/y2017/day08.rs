//! <https://adventofcode.com/2017/day/8>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Eq, Hash, PartialEq)]
enum Compare {
    LessThan,
    LessEqual,
    Equal,
    NotEqual,
    GreaterThan,
    GreaterEqual,
}

#[derive(Debug, Eq, Hash, PartialEq)]
struct Inst {
    register: String,
    offset: isize,
    cond_reg: String,
    cond_cmp: Compare,
    cond_val: isize,
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Inst>,
}

#[aoc(2017, 8)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^(\w+) (inc|dec) (-?\d+) if (\w+) (>=?|==|!=|<=?) (-?\d+)$");
        let segment = parser.captures(block).ok_or(ParseError)?;
        let mut offset = segment[3].parse::<isize>()?;
        if &segment[2] == "dec" {
            offset *= -1;
        }
        let cond_cmp: Compare = match &segment[5] {
            "<" => Compare::LessThan,
            "<=" => Compare::LessEqual,
            "==" => Compare::Equal,
            "!=" => Compare::NotEqual,
            ">" => Compare::GreaterThan,
            ">=" => Compare::GreaterEqual,
            _ => unreachable!(),
        };
        let cond_val: isize = segment[6].parse::<isize>()?;
        self.line.push(Inst {
            register: segment[1].to_string(),
            offset,
            cond_reg: segment[4].to_string(),
            cond_cmp,
            cond_val,
        });
        // self.line.push(segment[0].parse::<_>());
        Ok(())
    }
    fn after_insert(&mut self) {
        dbg!(&self.line.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut reg: HashMap<String, isize> = HashMap::new();
        for Inst {
            register,
            offset,
            cond_reg,
            cond_cmp,
            cond_val,
        } in self.line.iter()
        {
            let reg_val = *reg.entry(cond_reg.clone()).or_insert(0);
            let satisfied = match cond_cmp {
                Compare::LessThan => reg_val < *cond_val,
                Compare::LessEqual => reg_val <= *cond_val,
                Compare::Equal => reg_val == *cond_val,
                Compare::NotEqual => reg_val != *cond_val,
                Compare::GreaterThan => reg_val > *cond_val,
                Compare::GreaterEqual => reg_val >= *cond_val,
            };
            if satisfied {
                let reg = reg.entry(register.clone()).or_insert(0);
                *reg += offset;
            }
        }
        dbg!(*reg.values().max().unwrap_or(&0)) as usize
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut highest: isize = isize::MIN;
        let mut reg: HashMap<String, isize> = HashMap::new();
        for Inst {
            register,
            offset,
            cond_reg,
            cond_cmp,
            cond_val,
        } in self.line.iter()
        {
            let reg_val = *reg.entry(cond_reg.clone()).or_insert(0);
            let satisfied = match cond_cmp {
                Compare::LessThan => reg_val < *cond_val,
                Compare::LessEqual => reg_val <= *cond_val,
                Compare::Equal => reg_val == *cond_val,
                Compare::NotEqual => reg_val != *cond_val,
                Compare::GreaterThan => reg_val > *cond_val,
                Compare::GreaterEqual => reg_val >= *cond_val,
            };
            if satisfied {
                let reg = reg.entry(register.clone()).or_insert(0);
                *reg += offset;
                highest = highest.max(*reg);
            }
        }
        dbg!(highest) as usize
    }
}
