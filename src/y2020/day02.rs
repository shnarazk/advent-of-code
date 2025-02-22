//! <https://adventofcode.com/2020/day/2>
use crate::framework::{AdventOfCode, ParseError, aoc};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    line: Vec<(usize, usize, char, String)>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::{alpha1, newline, space1},
            combinator::{separated, seq},
            token::one_of,
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<(usize, usize, char, String)> {
        seq!(
            parse_usize,
            _: "-",
            parse_usize,
            _: space1,
            one_of('a'..='z'),
            _: ": ",
            alpha1,
        )
        .map(|(beg, end, lead, seq)| (beg, end, lead, seq.to_string()))
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<(usize, usize, char, String)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2020, 2)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> usize {
        self.line.iter().filter(check_line1).count()
    }
    fn part2(&mut self) -> usize {
        self.line.iter().filter(check_line2).count()
    }
}

fn check_line1((mi, ma, target, seq): &&(usize, usize, char, String)) -> bool {
    let occ = seq.chars().filter(|c| *c == *target).count();
    *mi <= occ && occ <= *ma
}

fn check_line2((pos1, pos2, ch, target): &&(usize, usize, char, String)) -> bool {
    let p1 = target.chars().nth(pos1 - 1) == Some(*ch);
    let p2 = target.chars().nth(pos2 - 1) == Some(*ch);
    p1 ^ p2
    // if p1 ^ p2 {
    //     println!(
    //         "OK: p1:{}=>{}, p2:{}=>{}, letter:{}, body: {}",
    //         pos1,
    //         target.chars().nth(pos1 - 1).unwrap(),
    //         pos2,
    //         target.chars().nth(pos2 - 1).unwrap(),
    //         ch,
    //         target
    //     );
    // } else {
    //     println!(
    //         "NG: p1:{}=>{}, p2:{}=>{}, letter:{}, body: {}",
    //         pos1,
    //         target.chars().nth(pos1 - 1).unwrap(),
    //         pos2,
    //         target.chars().nth(pos2 - 1).unwrap(),
    //         ch,
    //         target
    //     );
    // }
    // (p1 ^ p2) as usize
}
