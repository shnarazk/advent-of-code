//! <https://adventofcode.com/2015/day/7>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
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

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<Code>,
}

#[aoc(2015, 7)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    // fn header(&mut self, input: String) -> Result<Option<String>, ParseError> {
    //     let parser: Regex = Regex::new(r"^(.+)\n\n((.|\n)+)$").expect("wrong");
    //     let segment = parser.captures(input).ok_or(ParseError)?;
    //     for num in segment[1].split(',') {
    //         let _value = num.parse::<usize>()?;
    //     }
    //     Ok(Some(segment[2].to_string()))
    // }
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser1 = regex!(r"^([0-9]+|[a-z]+) -> ([a-z]+)$");
        let parser2 = regex!(r"^([0-9]+|[a-z]+) (AND|OR) ([0-9]+|[a-z]+) -> ([a-z]+)$");
        let parser3 = regex!(r"^([0-9]+|[a-z]+) (LSHIFT|RSHIFT) ([0-9]+) -> ([a-z]+)$");
        let parser4 = regex!(r"^NOT ([a-z]+) -> ([a-z]+)$");
        if let Ok(segment) = parser1.captures(block).ok_or(ParseError) {
            let op1: Id = Id::try_from(&segment[1])?;
            let op2: Id = Id::try_from(&segment[2])?;
            self.line.push(Code::Input(op1, op2));
            return Ok(());
        }
        if let Ok(segment) = parser2.captures(block).ok_or(ParseError) {
            let op1: Id = Id::try_from(&segment[1])?;
            let op2: Id = Id::try_from(&segment[3])?;
            let op3: Id = Id::try_from(&segment[4])?;
            self.line.push(match &segment[2] {
                "AND" => Code::And(op1, op2, op3),
                "OR" => Code::Or(op1, op2, op3),
                _ => unreachable!(),
            });
            return Ok(());
        }
        if let Ok(segment) = parser3.captures(block).ok_or(ParseError) {
            let op1: Id = Id::try_from(&segment[1])?;
            let op2: Id = Id::try_from(&segment[4])?;
            self.line.push(match &segment[2] {
                "LSHIFT" => Code::LShift(op1, segment[3].parse::<usize>()?, op2),
                "RSHIFT" => Code::RShift(op1, segment[3].parse::<usize>()?, op2),
                _ => unreachable!(),
            });
            return Ok(());
        }
        if let Ok(segment) = parser4.captures(block).ok_or(ParseError) {
            let op1: Id = Id::try_from(&segment[1])?;
            let op2: Id = Id::try_from(&segment[2])?;
            self.line.push(Code::Not(op1, op2));
            return Ok(());
        }
        dbg!(block);
        Err(ParseError)
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
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
