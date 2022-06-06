//! <https://adventofcode.com/2016/day/20>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        geometric::neighbors,
        line_parser, regex,
    },
    std::collections::HashSet,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<(usize, usize)>,
}

#[aoc(2016, 20)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let input = line_parser::to_usizes(block, '-')?;
        self.line.push((input[0], input[1]));
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut result = usize::MAX;
        let mut vals: Vec<usize> = Vec::new();
        for (l, h) in self.line.iter() {
            vals.push(*l);
            vals.push(*h);
        }
        vals.sort_unstable();
        for p in vals.iter() {
            for x in [p.saturating_sub(1), p + 1] {
                if self.line.iter().all(|(l, h)| x < *l || *h < x) {
                    result = result.min(x);
                }
            }
        }
        result
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut result: usize = 0;
        let mut pres: HashSet<usize> = HashSet::new();
        for (l, h) in self.line.iter() {
            // assert!(*l < *h);
            pres.insert(*l);
            pres.insert(*h);
        }
        let mut vals: Vec<usize> = Vec::new();
        for v in pres.iter() {
            vals.push(*v);
        }
        for (l, h) in self.line.iter() {
            if l == h {
                dbg!(l);
                vals.push(*l);
            }
        }
        vals.sort_unstable();
        let mut carry = false;
        // dbg!(&vals[0..10]);
        for vec in vals.windows(2) {
            let r0 = vec[0];
            let r1 = vec[1];
            if self
                .line
                .iter()
                .any(|(l, h)| *l <= r0 && r0 <= *h && *l <= r1 && r1 <= *h)
            {
                result += r1 - r0;
                carry = true;
            } else {
                result += carry as usize;
                carry = false;
            }
        }
        if carry {
            result += 1;
        }
        dbg!(result);
        u32::MAX as usize - result
    }
}

#[cfg(feature = "y2016")]
#[cfg(test)]
mod test {
    use {
        super::*,
        crate::framework::{Answer, Description},
    };

    // #[test]
    // fn test_part1() {
    //     assert_eq!(
    //         Puzzle::solve(Description::TestData("".to_string()), 1),
    //         Answer::Part1(0)
    //     );
    // }
}
