//! <https://adventofcode.com/2021/day/8>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Debug, PartialEq)]
struct DataSegment {
    pattern: Vec<Vec<char>>,
    target: Vec<Vec<char>>,
}

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<DataSegment>,
}

fn s2i(ch: char) -> usize {
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
fn deduce(pattern: &[Vec<char>], table: &[usize; 7]) -> [usize; 7] {
    // from used mnemonic to true mnemonic
    let mut real_mnemonic: [Option<usize>; 7] = [None; 7];

    // fix unique occurs (4 => 'e'), (6 => 'b'), (9 => 'f')
    for (i, n) in table.iter().enumerate() {
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
                    real_mnemonic[s2i(*c)] = Some(0); // 0 == 'a'
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
    assert!(
        real_mnemonic.iter().all(|k| k.is_some()),
        "{:?}\n{:?}",
        pattern,
        real_mnemonic
    );
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
    if vec.len() == 6 && vec.iter().all(|d| [0, 1, 2, 4, 5, 6].contains(d)) {
        return 0;
    }
    if vec.len() == 2 && vec.iter().all(|d| [2, 5].contains(d)) {
        return 1;
    }
    if vec.len() == 5 && vec.iter().all(|d| [0, 2, 3, 4, 6].contains(d)) {
        return 2;
    }
    if vec.len() == 5 && vec.iter().all(|d| [0, 2, 3, 5, 6].contains(d)) {
        return 3;
    }
    if vec.len() == 4 && vec.iter().all(|d| [1, 2, 3, 5].contains(d)) {
        return 4;
    }
    if vec.len() == 5 && vec.iter().all(|d| [0, 1, 3, 5, 6].contains(d)) {
        return 5;
    }
    if vec.len() == 6 && vec.iter().all(|d| [0, 1, 3, 4, 5, 6].contains(d)) {
        return 6;
    }
    if vec.len() == 3 && vec.iter().all(|d| [0, 2, 5].contains(d)) {
        return 7;
    }
    if vec.len() == 7 && vec.iter().all(|d| [0, 1, 2, 3, 4, 5, 6].contains(d)) {
        return 8;
    }
    if vec.len() == 6 && vec.iter().all(|d| [0, 1, 2, 3, 5, 6].contains(d)) {
        return 9;
    }
    panic!("{:?}", vec);
}

mod parser {
    use {
        super::DataSegment,
        winnow::{
            ascii::{alpha1, newline, space1},
            combinator::{separated, seq},
            PResult, Parser,
        },
    };

    fn parse_line(s: &mut &str) -> PResult<DataSegment> {
        seq!(
            separated::<_,_, Vec<&str>,_,_,_,_>(1.., alpha1, space1),
            _: " | ",
            separated::<_,_, Vec<&str>,_,_,_,_>(1.., alpha1, space1),
        )
        .map(|(a, b)| DataSegment {
            pattern: a.iter().map(|s| s.chars().collect::<Vec<_>>()).collect(),
            target: b.iter().map(|s| s.chars().collect::<Vec<_>>()).collect(),
        })
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> PResult<Vec<DataSegment>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2021, 8)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parser::parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn part1(&mut self) -> usize {
        self.line
            .iter()
            .map(|v| {
                v.target
                    .iter()
                    .filter(|p| [2, 3, 4, 7].contains(&p.len()))
                    .count()
            })
            .sum()
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
            total += value;
        }
        total
    }
}
