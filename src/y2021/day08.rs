use crate::{AdventOfCode, Description, ParseError, TryParse};
use lazy_static::lazy_static;
use regex::Regex;

#[derive(Debug, PartialEq)]
struct DataSegment {
    pattern: Vec<Vec<char>>,
    target: Vec<Vec<char>>,
}

impl TryParse for DataSegment {
    fn parse(s: &str) -> Result<Self, ParseError> {
        lazy_static! {
            static ref PARSER: Regex = Regex::new(r"^([ a-g]+)\|([ a-g]+)$").expect("wrong");
        }
        let segment = PARSER.captures(s).ok_or(ParseError)?;
        let mut pattern: Vec<Vec<char>> = Vec::new();
        let mut target: Vec<Vec<char>> = Vec::new();
        for w in segment[1].trim().split(' ') {
            pattern.push(w.chars().collect::<Vec<_>>());
        }
        for w in segment[2].trim().split(' ') {
            target.push(w.chars().collect::<Vec<_>>());
        }
        Ok(DataSegment { pattern, target })
    }
}

#[derive(Debug, PartialEq)]
struct Puzzle {
    line: Vec<DataSegment>,
}

fn s2i (ch: char) -> usize {
    match ch {
        'a' => 0,
        'b' => 1,
        'c' => 2,
        'd' => 3,
        'e' => 4,
        'f' => 5,
        'g' => 6,
        _ => panic!("strange char"),
    }
}

//                 (4, 'e'),
//                 (6, 'b'),
//                 (7, 'd'),
//                 (7, 'g'),
//                 (8, 'a'),
//                 (8, 'c'),
//                 (9, 'f'),
fn deduce (pattern: &[Vec<char>], table: &[usize; 7]) -> [usize; 7] {
    // from used mnemonic to true mnemonic
    let mut real_mnemonic: [Option<usize>; 7] = [None; 7];

    // fix unique occurs (4 => 'e'), (6 => 'b'), (9 => 'f')
    for (i,n) in table.iter().enumerate() {
        match n {
            4 => real_mnemonic[i] = Some(4), // 4 == 'e'
            6 => real_mnemonic[i] = Some(1), // 1 == 'b'
            9 => real_mnemonic[i] = Some(5), // 5 == 'f'
            _ => (),
        }
    }
    'stage2: for p in pattern.iter() {
        if p.len() == 2 {
            // deduce from digit which len == 2: 'f' => 'c'
            for c in p.iter() {
                if real_mnemonic[s2i(*c)].is_none() {
                    real_mnemonic[s2i(*c)] = Some(2); // 2 == 'c'
                    break 'stage2;
                }
            }
        }
    }
    // deduce from digit 2: 'f' & 'c' => 'a'
    'stage3: for p in pattern.iter() {
        if p.len() == 3 {
            for c in p.iter() {
                if real_mnemonic[s2i(*c)].is_none() {
                    real_mnemonic[s2i(*c)] = Some(0);  // 0 == 'a'
                    break 'stage3;
                }
            }
        }
    }
    // deduce from digit 4: 'b' & 'c' => 'd'
    'stage4: for p in pattern.iter() {
        if p.len() == 4 && p.iter().any(|c| real_mnemonic[s2i(*c)].is_none()) {
            for c in p.iter() {
                if real_mnemonic[s2i(*c)].is_none() {
                    real_mnemonic[s2i(*c)] = Some(3); // 3 == 'd'
                    break 'stage4;
                }
            }
        }
    }
    // fill the last one
    for i in real_mnemonic.iter_mut() {
        if i.is_none() {
            *i = Some(6);
            break;
        } 
    }
    assert!(real_mnemonic.iter().all(|k| k.is_some()), "{:?}\n{:?}", pattern, real_mnemonic);
    [
        real_mnemonic[0].unwrap(),
        real_mnemonic[1].unwrap(),
        real_mnemonic[2].unwrap(),
        real_mnemonic[3].unwrap(),
        real_mnemonic[4].unwrap(),
        real_mnemonic[5].unwrap(),
        real_mnemonic[6].unwrap(),
    ]
}

fn segments_to_num(vec: &[usize]) -> usize {
    if vec.len() == 6 && vec.iter().all(|d| [0, 1, 2, 4, 5, 6].contains(d)) { return 0; }
    if vec.len() == 2 && vec.iter().all(|d| [2, 5].contains(d)) { return 1; }
    if vec.len() == 5 && vec.iter().all(|d| [0, 2, 3, 4, 6].contains(d)) { return 2; }
    if vec.len() == 5 && vec.iter().all(|d| [0, 2, 3, 5, 6].contains(d)) { return 3; }
    if vec.len() == 4 && vec.iter().all(|d| [1, 2, 3, 5].contains(d)) { return 4; }
    if vec.len() == 5 && vec.iter().all(|d| [0, 1, 3, 5, 6].contains(d)) { return 5; }
    if vec.len() == 6 && vec.iter().all(|d| [0, 1, 3, 4, 5, 6].contains(d)) { return 6; }
    if vec.len() == 3 && vec.iter().all(|d| [0, 2, 5].contains(d)) { return 7; }
    if vec.len() == 7 && vec.iter().all(|d| [0, 1, 2, 3, 4, 5, 6].contains(d)) { return 8; }
    if vec.len() == 6 && vec.iter().all(|d| [0, 1, 2, 3, 5, 6].contains(d)) { return 9; }
    panic!("{:?}", vec);
}

impl AdventOfCode for Puzzle {
    type Segment = DataSegment;
    type Output1 = usize;
    type Output2 = usize;
    const YEAR: usize = 2021;
    const DAY: usize = 8;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self {
            line: Vec::new(),
        }
    }
    fn insert(&mut self, object: Self::Segment) {
        self.line.push(object);
    }
    fn after_insert(&mut self) {
    }
    fn part1(&mut self) -> usize {
        self.line.iter().map(|v| v.target.iter().filter(|p| [2, 3, 4, 7].contains(&p.len())).count()).sum()
    }
    fn part2(&mut self) -> usize {
        let mut total = 0;
        for v in self.line.iter() {
            let mut table = [0; 7];
            for (i, ch) in ('a'..='g').enumerate() {
                table[i] = v.pattern.iter().filter(|set| set.contains(&ch)).count();
            }
            let decode = deduce(&v.pattern, &table);
            let mut value: usize = 0;
            for ss in v.target.iter() {
                value *= 10;
                value += segments_to_num(&ss.iter().map(|s| decode[s2i(*s)]).collect::<Vec<_>>());
            }
            // dbg!(value);
            total += value;
        }
        total
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::solve(&desc, part));
}
