//! <https://adventofcode.com/2023/day/1>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<u8>>,
    line2: Vec<Vec<u8>>,
}

static SUBST: once_cell::sync::OnceCell<Vec<(Vec<u8>, u8)>> = once_cell::sync::OnceCell::new();

#[aoc(2023, 1)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let subst = SUBST.get_or_init(|| {
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
        let mut b = block.bytes().collect::<Vec<_>>();
        self.line.push(b.clone());
        (0..b.len()).for_each(|i| {
            for (r, s) in subst {
                if b[i..].starts_with(&r) {
                    b[i] = *s;
                    break;
                }
            }
        });
        self.line2.push(b);
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
            10 * (*d[0] - ('0' as u8)) as usize + (*d[d.len() - 1] - ('0' as u8)) as usize
        })
        .sum()
}
