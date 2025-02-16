//! <https://adventofcode.com/2016/day/04>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[allow(clippy::type_complexity)]
pub struct Puzzle {
    line: Vec<(HashMap<char, usize>, usize, Vec<char>, Vec<Vec<char>>)>,
}

mod parser {
    use {
        crate::parser::parse_usize,
        std::collections::HashMap,
        winnow::{
            ascii::{alpha1, newline},
            combinator::{separated, seq},
            ModalResult, Parser,
        },
    };

    #[allow(clippy::type_complexity)]
    fn parse_line(
        s: &mut &str,
    ) -> ModalResult<(HashMap<char, usize>, usize, Vec<char>, Vec<Vec<char>>)> {
        seq!(
            separated(1.., alpha1, '-').map(|v: Vec<&str>| v),
            _: "-",
            parse_usize,
            _: "[",
            alpha1,
            _: "]"
        )
        .map(|(v, sector_id, checksum)| {
            let mut letters: HashMap<char, usize> = HashMap::new();
            for s in v.iter() {
                for c in s.chars() {
                    *letters.entry(c).or_insert(0) += 1;
                }
            }
            let tokens: Vec<Vec<char>> = v.iter().map(|s| s.chars().collect()).collect();
            (
                letters,
                sector_id,
                checksum.chars().collect::<Vec<char>>(),
                tokens,
            )
        })
        .parse_next(s)
    }

    #[allow(clippy::type_complexity)]
    pub fn parse(
        s: &mut &str,
    ) -> ModalResult<Vec<(HashMap<char, usize>, usize, Vec<char>, Vec<Vec<char>>)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2016, 4)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parser::parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.line
            .iter()
            .filter(|(letters, _, checksum, _)| {
                let mut v = letters
                    .iter()
                    .map(|(l, n)| (-(*n as isize), l))
                    .collect::<Vec<_>>();
                v.sort_unstable();
                let valids = v
                    .iter()
                    .take(5)
                    .map(|(_, l)| l)
                    .copied()
                    .collect::<Vec<_>>();
                checksum.iter().all(|c| valids.contains(&c))
            })
            .map(|e| e.1)
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.line
            .iter()
            .filter(|(letters, _, checksum, _)| {
                let mut v = letters
                    .iter()
                    .map(|(l, n)| (-(*n as isize), l))
                    .collect::<Vec<_>>();
                v.sort_unstable();
                let valids = v
                    .iter()
                    .take(5)
                    .map(|(_, l)| l)
                    .copied()
                    .collect::<Vec<_>>();
                checksum.iter().all(|c| valids.contains(&c))
            })
            .filter(|(_, sector_id, _, tokens)| {
                let mut words = Vec::new();
                for token in tokens.iter() {
                    let word = token
                        .iter()
                        .map(|c| {
                            (((((*c as u8 - b'a') as usize) + sector_id) % 26) as u8 + b'a') as char
                        })
                        .collect::<String>();
                    words.push(word);
                }
                if words.join("").contains("northpole") {
                    // println!("{sector_id}, {:?}", words);
                    return true;
                }
                false
            })
            .map(|e| e.1)
            .collect::<Vec<usize>>()[0]
    }
}
