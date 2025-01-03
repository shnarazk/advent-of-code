//! <https://adventofcode.com/2016/day/04>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::collections::HashMap,
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[allow(clippy::type_complexity)]
pub struct Puzzle {
    line: Vec<(HashMap<char, usize>, usize, Vec<char>, Vec<Vec<char>>)>,
}

#[aoc(2016, 4)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(r"^([0-9]+)\[([a-z]+)\]$");
        let mut letters: HashMap<char, usize> = HashMap::new();
        let mut sector_id: usize = 0;
        let mut checksum: Vec<char> = Vec::new();
        let mut tokens: Vec<Vec<char>> = Vec::new();
        for token in block.split('-') {
            if let Some(segment) = parser.captures(token) {
                sector_id = segment[1].parse::<usize>()?;
                checksum = segment[2].chars().collect::<Vec<char>>();
                break;
            } else {
                tokens.push(token.chars().collect::<Vec<_>>());
                for c in token.chars() {
                    *letters.entry(c).or_insert(0) += 1;
                }
            }
        }
        self.line.push((letters, sector_id, checksum, tokens));
        Ok(())
    }
    fn end_of_data(&mut self) {
        // dbg!(&self.line);
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
