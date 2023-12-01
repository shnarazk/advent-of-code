//! <https://adventofcode.com/2023/day/1>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    line2: Vec<Vec<u8>>,
}

#[aoc(2023, 1)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        static SUBST: once_cell::sync::OnceCell<Vec<(Vec<u8>, u8)>> =
            once_cell::sync::OnceCell::new();
        SUBST.get_or_init(|| {
            vec![
                (b"one".to_vec(), b'1'),
                (b"two".to_vec(), b'2'),
                (b"three".to_vec(), b'3'),
                (b"four".to_vec(), b'4'),
                (b"five".to_vec(), b'5'),
                (b"six".to_vec(), b'6'),
                (b"seven".to_vec(), b'7'),
                (b"eight".to_vec(), b'8'),
                (b"nine".to_vec(), b'9'),
            ]
        });
        let b = block.bytes().collect::<Vec<_>>();
        self.line.push(b.clone());
        let acc: Vec<u8> = (0..b.len())
            .map(|i| {
                for (r, s) in SUBST.get().unwrap() {
                    if b[i..].starts_with(&r) {
                        return *s;
                    }
                }
                b[i]
            })
            .collect::<Vec<_>>();
        self.line2.push(acc);
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        sum(&self.line)
    }
    fn part2(&mut self) -> Self::Output2 {
        sum(&self.line2)
    }
}

fn sum(l: &[Vec<u8>]) -> usize {
    l.iter()
        .map(|v| {
            let d = v
                .iter()
                .filter(|c| (**c as char).is_digit(10))
                .collect::<Vec<_>>();
            String::from_utf8(vec![*d[0], *d[d.len() - 1]])
                .unwrap()
                .parse::<usize>()
                .unwrap()
        })
        .sum()
}
