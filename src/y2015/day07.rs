//! <https://adventofcode.com/2015/day/7>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Eq, PartialEq)]
enum Id {
    Const(usize),
    Wire(String),
}

impl TryFrom<&str> for Id {
    type Error = ParseError;
    fn try_from(s: &str) -> Result<Self, ParseError> {
        if s.chars().next().unwrap().is_ascii_digit() {
            Ok(Id::Const(s.parse::<usize>()?))
        } else {
            Ok(Id::Wire(s.to_string()))
        }
    }
}

impl Id {
    fn determined(&self, hash: &HashMap<String, usize>) -> bool {
        match self {
            Id::Const(_) => true,
            Id::Wire(s) if hash.contains_key(s) => true,
            _ => false,
        }
    }
    fn get(&self, hash: &HashMap<String, usize>) -> usize {
        match self {
            Id::Const(n) => *n,
            Id::Wire(s) => *hash.get(s).unwrap(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Code {
    Input(Id, Id),
    And(Id, Id, Id),
    Or(Id, Id, Id),
    LShift(Id, usize, Id),
    RShift(Id, usize, Id),
    Not(Id, Id),
}

impl Code {
    fn determined(&self, hash: &HashMap<String, usize>) -> bool {
        match self {
            Code::Input(op1, _) => op1.determined(hash),
            Code::And(op1, op2, _) => op1.determined(hash) && op2.determined(hash),
            Code::Or(op1, op2, _) => op1.determined(hash) && op2.determined(hash),
            Code::LShift(op1, _, _) => op1.determined(hash),
            Code::RShift(op1, _, _) => op1.determined(hash),
            Code::Not(op1, _) => op1.determined(hash),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<Code>,
}

mod parser {
    use {
        super::*,
        crate::parser::parse_usize,
        winnow::{
            ascii::{alpha1, newline},
            combinator::{alt, separated, seq},
            ModalResult, Parser,
        },
    };

    fn parse_id(s: &mut &str) -> ModalResult<Id> {
        alt((
            parse_usize.map(Id::Const),
            alpha1.map(|s: &str| Id::Wire(s.to_string())),
        ))
        .parse_next(s)
    }

    fn parse_line(s: &mut &str) -> ModalResult<Code> {
        alt((
            seq!(parse_id, _: " -> ", parse_id).map(|(a, b)| Code::Input(a, b)),
            seq!(parse_id, _: " AND ", parse_id, _: " -> ", parse_id)
                .map(|(a, b, c)| Code::And(a, b, c)),
            seq!(parse_id, _: " OR ", parse_id, _: " -> ", parse_id)
                .map(|(a, b, c)| Code::Or(a, b, c)),
            seq!(parse_id, _: " LSHIFT ", parse_usize, _: " -> ", parse_id)
                .map(|(a, b, c)| Code::LShift(a, b, c)),
            seq!(parse_id, _: " RSHIFT ", parse_usize, _: " -> ", parse_id)
                .map(|(a, b, c)| Code::RShift(a, b, c)),
            seq!(_: "NOT ", parse_id, _: " -> ", parse_id).map(|(a, b)| Code::Not(a, b)),
        ))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Code>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2015, 7)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut value: HashMap<String, usize> = HashMap::new();
        // let mut count = 0;
        while let Some(code) = self.line.pop() {
            // count += 1;
            // assert!(count < 20);
            if code.determined(&value) {
                // println!("{:?} => {:?}", code, code.determined(&value));
                assert!(match code {
                    Code::Input(op1, Id::Wire(s)) => value.insert(s, op1.get(&value)),
                    Code::And(op1, op2, Id::Wire(s)) =>
                        value.insert(s, op1.get(&value) & op2.get(&value)),
                    Code::Or(op1, op2, Id::Wire(s)) =>
                        value.insert(s, op1.get(&value) | op2.get(&value)),
                    Code::LShift(op1, n, Id::Wire(s)) => value.insert(s, op1.get(&value) << n),
                    Code::RShift(op1, n, Id::Wire(s)) => value.insert(s, op1.get(&value) >> n),
                    Code::Not(op1, Id::Wire(s)) => value.insert(s, !op1.get(&value)),
                    _ => None,
                }
                .is_none());
            } else {
                self.line.insert(0, code);
            }
        }
        *value.get("a").expect("no a")
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut line = self.line.clone();
        let b_value = self.part1();
        line.retain(|c| !matches!(c, Code::Input(Id::Const(_), Id::Wire(b)) if b == "b"));
        line.push(Code::Input(Id::Const(b_value), Id::Wire("b".to_string())));
        dbg!(line.len());
        self.line = line;
        self.part1()
    }
}

#[cfg(feature = "y2015")]
#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_ids() {
        assert!(Id::try_from("0").is_ok());
        assert_eq!(Id::try_from("0"), Ok(Id::Const(0)));
        assert!(Id::try_from("a").is_ok());
        assert_eq!(Id::try_from("a"), Ok(Id::Wire("a".to_string())));
        assert!(Id::try_from("0").unwrap().determined(&HashMap::new()));
        assert!(!Id::try_from("a").unwrap().determined(&HashMap::new()));
    }
}
