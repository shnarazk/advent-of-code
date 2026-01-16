//! <https://adventofcode.com/2023/day/1>
use crate::framework::{AdventOfCode, ParseError, aoc};
use std::simd::{Simd, cmp::SimdPartialOrd};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    table: [usize; 256],
    subst: Vec<Vec<u8>>,
    sum1: usize,
    sum2: usize,
}

impl Default for Puzzle {
    fn default() -> Self {
        let mut table = [0usize; 256];
        for i in 1..=9 {
            table[b'0' as usize + i] = i;
        }
        for c in [b'e', b'f', b'n', b'o', b's', b't'] {
            table[c as usize] = 10;
        }
        let subst = vec![
            b"one".to_vec(),
            b"two".to_vec(),
            b"three".to_vec(),
            b"four".to_vec(),
            b"five".to_vec(),
            b"six".to_vec(),
            b"seven".to_vec(),
            b"eight".to_vec(),
            b"nine".to_vec(),
        ];
        Puzzle {
            table,
            subst,
            sum1: 0,
            sum2: 0,
        }
    }
}

#[aoc(2023, 1)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
        for l in input.lines() {
            let b = l.bytes().collect::<Vec<_>>();
            let len = b.len();
            for dir in [0, 1] {
                let scale = 10 - dir * 9;
                let mut not_found = true;
                for ii in 0..len {
                    let i = if dir == 1 { len - ii - 1 } else { ii };
                    let mut value = self.table[b[i] as usize];
                    if value == 0 {
                        continue;
                    }
                    if value < 10 {
                        value *= scale;
                        if not_found {
                            self.sum2 += value;
                        }
                        self.sum1 += value;
                        break;
                    }
                    if not_found {
                        for (j, r) in self.subst.iter().enumerate() {
                            if b[i..].starts_with(r) {
                                self.sum2 += scale * (j + 1);
                                not_found = false;
                                break;
                            }
                        }
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

pub fn first_last_digit_simd(buf: &[u8]) -> Option<(u8, u8)> {
    const LANES: usize = 16; // NEON-friendly width
    type V = Simd<u8, LANES>;

    let mut i = 0usize;
    let mut first: Option<u8> = None;
    let mut last: Option<u8> = None;

    let v0 = V::splat(b'0');
    let v9 = V::splat(b'9');

    while i + LANES <= buf.len() {
        let v = V::from_slice(&buf[i..i + LANES]);

        let is_digit = v.simd_ge(v0) & v.simd_le(v9);

        // For LANES=16 this is a u16 mask. Bit k corresponds to lane k.
        let mask: u16 = is_digit.to_bitmask().try_into().unwrap();

        if mask != 0 {
            if first.is_none() {
                let lane = mask.trailing_zeros() as usize; // 0..15
                first = Some(buf[i + lane] - b'0');
            }

            let lane = 15 - (mask.leading_zeros() as usize); // last set bit index 0..15
            last = Some(buf[i + lane] - b'0');
        }

        i += LANES;
    }

    // Scalar tail
    while i < buf.len() {
        let c = buf[i];
        if (b'0'..=b'9').contains(&c) {
            let d = c - b'0';
            if first.is_none() {
                first = Some(d);
            }
            last = Some(d);
        }
        i += 1;
    }

    first.zip(last)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_first_last_digit_simd() {
        assert_eq!(first_last_digit_simd(b""), None);
        assert_eq!(first_last_digit_simd(b"abc"), None);
        assert_eq!(first_last_digit_simd(b"a1bc"), Some((1, 1)));
        assert_eq!(first_last_digit_simd(b"a1b2c3"), Some((1, 3)));
        assert_eq!(first_last_digit_simd(b"9xxx0"), Some((9, 0)));
    }
}
