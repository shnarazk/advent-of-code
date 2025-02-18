//! <https://adventofcode.com/2017/day/8>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Compare {
    LessThan,
    LessEqual,
    Equal,
    NotEqual,
    GreaterThan,
    GreaterEqual,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Inst {
    register: String,
    offset: isize,
    cond_reg: String,
    cond_cmp: Compare,
    cond_val: isize,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Inst>,
}

mod parser {
    use {
        super::*,
        crate::parser::parse_isize,
        winnow::{
            ascii::{alpha1, newline},
            combinator::{alt, separated, seq},
            ModalResult, Parser,
        },
    };

    fn parse_inst(s: &mut &str) -> ModalResult<Inst> {
        alt((
            seq!(alpha1, alt((" inc ", " dec ")).map(|s| s == " inc "), parse_isize, _: " if ", alpha1, _: " < ", parse_isize)
            .map(|(register, inc, offset, cond_reg, cond_val)| Inst {
                register: register.to_string(),
                offset: if inc { offset } else { -offset },
                cond_reg: cond_reg.to_string(),
                cond_cmp: Compare::LessThan,
                cond_val,
            }),
            seq!(alpha1, alt((" inc ", " dec ")).map(|s| s == " inc "), parse_isize, _: " if ", alpha1, _: " <= ", parse_isize)
            .map(|(register, inc, offset, cond_reg, cond_val)| Inst {
                register: register.to_string(),
                offset: if inc { offset } else { -offset },
                cond_reg: cond_reg.to_string(),
                cond_cmp: Compare::LessEqual,
                cond_val,
            }),
            seq!(alpha1, alt((" inc ", " dec ")).map(|s| s == " inc "), parse_isize, _: " if ", alpha1, _: " <= ", parse_isize)
            .map(|(register, inc, offset, cond_reg, cond_val)| Inst {
                register: register.to_string(),
                offset: if inc { offset } else { -offset },
                cond_reg: cond_reg.to_string(),
                cond_cmp: Compare::LessEqual,
                cond_val,
            }),
            seq!(alpha1, alt((" inc ", " dec ")).map(|s| s == " inc "), parse_isize, _: " if ", alpha1, _: " == ", parse_isize)
            .map(|(register, inc, offset, cond_reg, cond_val)| Inst {
                register: register.to_string(),
                offset: if inc { offset } else { -offset },
                cond_reg: cond_reg.to_string(),
                cond_cmp: Compare::Equal,
                cond_val,
            }),
            seq!(alpha1,  alt((" inc ", " dec ")).map(|s| s == " inc "), parse_isize, _: " if ", alpha1, _: " != ", parse_isize)
            .map(|(register, inc, offset, cond_reg, cond_val)| Inst {
                register: register.to_string(),
                offset: if inc { offset } else { -offset },
                cond_reg: cond_reg.to_string(),
                cond_cmp: Compare::NotEqual,
                cond_val,
            }),
            seq!(alpha1, alt((" inc ", " dec ")).map(|s| s == " inc "), parse_isize, _: " if ", alpha1, _: " > ", parse_isize)
            .map(|(register, inc, offset, cond_reg, cond_val)| Inst {
                register: register.to_string(),
                offset: if inc { offset } else { -offset },
                cond_reg: cond_reg.to_string(),
                cond_cmp: Compare::GreaterThan,
                cond_val,
            }),
            seq!(alpha1, alt((" inc ", " dec ")).map(|s| s == " inc "), parse_isize, _: " if ", alpha1, _: " >= ", parse_isize)
            .map(|(register, inc, offset, cond_reg, cond_val)| Inst {
                register: register.to_string(),
                offset: if inc { offset } else { -offset },
                cond_reg: cond_reg.to_string(),
                cond_cmp: Compare::GreaterEqual,
                cond_val,
            }),
        ))
            .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Inst>> {
        separated(1.., parse_inst, newline).parse_next(s)
    }
}

#[aoc(2017, 8)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parser::parse(&mut input.as_str())?;
        Self::parsed()
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
        *reg.values().max().unwrap_or(&0) as usize
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
        highest as usize
    }
}
