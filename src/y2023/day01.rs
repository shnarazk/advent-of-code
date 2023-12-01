//! <https://adventofcode.com/2023/day/1>
use crate::framework::{aoc, AdventOfCode, ParseError};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    sum1: usize,
    sum2: usize,
}

static SUBST: once_cell::sync::OnceCell<Vec<Vec<u8>>> = once_cell::sync::OnceCell::new();

#[aoc(2023, 1)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let subst = SUBST.get_or_init(|| {
            vec![
                b"one".to_vec(),
                b"two".to_vec(),
                b"three".to_vec(),
                b"four".to_vec(),
                b"five".to_vec(),
                b"six".to_vec(),
                b"seven".to_vec(),
                b"eight".to_vec(),
                b"nine".to_vec(),
            ]
        });
        let firsts = [b'e', b'f', b'n', b'o', b's', b't'];
        let b = block.bytes().collect::<Vec<_>>();
        let mut not_found = true;
        for i in 0..b.len() {
            let x = b[i] - ('0' as u8);
            if 1 <= x && x <= 9 {
                let n = 10 * (x as usize);
                if not_found {
                    self.sum2 += n;
                }
                self.sum1 += n;
                break;
            }
            if not_found && firsts.contains(&b[i]) {
                for (j, r) in subst.iter().enumerate() {
                    if b[i..].starts_with(&r) {
                        self.sum2 += 10 * (j + 1);
                        not_found = false;
                        break;
                    }
                }
            }
        }
        not_found = true;
        for i in (0..b.len()).rev() {
            let x = b[i] - ('0' as u8);
            if 1 <= x && x <= 9 {
                let n = x as usize;
                if not_found {
                    self.sum2 += n;
                }
                self.sum1 += n;
                break;
            }
            if not_found && firsts.contains(&b[i]) {
                for (j, r) in subst.iter().enumerate() {
                    if b[i..].starts_with(&r) {
                        self.sum2 += j + 1;
                        not_found = false;
                        break;
                    }
                }
            }
        }
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        self.sum1
    }
    fn part2(&mut self) -> Self::Output2 {
        self.sum2
    }
}
