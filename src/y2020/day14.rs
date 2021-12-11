use {
    crate::y2020::traits::{Description, ProblemObject, ProblemSolver},
    lazy_static::lazy_static,
    regex::Regex,
    std::collections::HashMap,
};

pub fn day14(part: usize, desc: Description) {
    dbg!(Setting::parse(desc).run(part));
}

#[derive(Clone, Debug, PartialEq)]
enum OP {
    Mask(usize, usize, Vec<usize>),
    Set(usize, usize),
}

impl ProblemObject for OP {
    fn parse(str: &str) -> Option<Self> {
        lazy_static! {
            static ref MASK: Regex = Regex::new(r"^mask = ((X|0|1)+)").expect("wrong");
            static ref SET: Regex = Regex::new(r"^mem\[(\d+)\] = (\d+)").expect("wrong");
        }
        if let Some(m) = MASK.captures(str) {
            let zeros = m[1]
                .chars()
                .fold(0, |sum, letter| sum * 2 + if letter == '0' { 1 } else { 0 });
            let ones = m[1]
                .chars()
                .fold(0, |sum, letter| sum * 2 + if letter == '1' { 1 } else { 0 });
            let wilds = m[1]
                .chars()
                .enumerate()
                .fold(Vec::new(), |mut v, (i, letter)| {
                    if letter == 'X' {
                        v.push(35 - i);
                    }
                    v
                });
            return Some(OP::Mask(zeros, ones, wilds));
        }
        if let Some(m) = SET.captures(str) {
            let address = m[1].parse::<usize>().unwrap();
            let val = m[2].parse::<usize>().unwrap();
            return Some(OP::Set(address, val));
        }
        None
    }
}

impl OP {
    fn apply1_to(&self, v: usize) -> usize {
        if let OP::Mask(zs, os, _) = self {
            (v | os) & !zs
        } else {
            v
        }
    }
    fn apply2_to(&self, v: usize) -> Vec<usize> {
        if let OP::Mask(_, os, ms) = self {
            let base = v | os;
            let mut vec = Vec::new();
            for mut i in 0..2_i32.pow(ms.len() as u32) as usize {
                let mut addr = base;
                for loc in ms.iter() {
                    addr &= !(1 << loc);
                    addr |= (i % 2) << loc;
                    i /= 2;
                }
                vec.push(addr);
            }
            vec
        } else {
            vec![v]
        }
    }
}

#[derive(Debug, PartialEq)]
struct Setting {
    mask: OP,
    code: Vec<OP>,
}

impl ProblemSolver<OP, usize, usize> for Setting {
    const YEAR: usize = 2020;
    const DAY: usize = 14;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Setting {
            mask: OP::Mask(0, 0, vec![]),
            code: Vec::new(),
        }
    }
    fn insert(&mut self, op: OP) {
        self.code.push(op);
    }
    fn part1(&mut self) -> usize {
        let mut mem: HashMap<usize, usize> = HashMap::new();
        for op in self.code.iter() {
            match op {
                OP::Mask(_, _, _) => {
                    self.mask = op.clone();
                }
                OP::Set(a, v) => {
                    *mem.entry(*a).or_insert(0) = self.mask.apply1_to(*v);
                }
            }
        }
        mem.values().sum::<usize>()
    }
    fn part2(&mut self) -> usize {
        let mut mem: HashMap<usize, usize> = HashMap::new();
        for op in self.code.iter() {
            match op {
                OP::Mask(_, _, _) => {
                    self.mask = op.clone();
                }
                OP::Set(a, v) => {
                    for addr in self.mask.apply2_to(*a).iter() {
                        *mem.entry(*addr).or_insert(0) = *v;
                    }
                }
            }
        }
        mem.values().sum::<usize>()
    }
}

#[cfg(test)]
mod test {
    use {
        super::*,
        crate::y2020::traits::{Answer, Description},
    };

    #[test]
    fn test_part1() {
        assert_eq!(
            Setting::parse(Description::FileTag("test1".to_string())).run(1),
            Answer::Part1(165)
        );
    }
    #[test]
    fn test_part2() {
        assert_eq!(
            Setting::parse(Description::FileTag("test2".to_string())).run(2),
            Answer::Part2(208)
        );
    }
}
