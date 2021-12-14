use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    md5::{Digest, Md5},
};

#[derive(Debug, Default)]
pub struct Puzzle {
    line: String,
}

#[aoc(2015, 4)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        self.line = block.to_string();
        Ok(())
    }
    fn after_insert(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        // self.line = "abcdef".to_string();
        // self.line = "pqrstuv".to_string();
        for i in 0.. {
            let target: String = format!("{}{}", self.line, i);
            let mut hasher = Md5::new();
            hasher.update(&target);
            let d = hasher
                .finalize()
                .iter()
                .map(|n| format!("{:0>2x}", n))
                .collect::<Vec<String>>()
                .join("");
            if d.starts_with("00000") {
                dbg!(i, d);
                return i;
            }
        }
        // for n in &hasher.finalize()[..] {
        //     print!("{:0>2X}", n);
        // }
        0
    }
    fn part2(&mut self) -> Self::Output2 {
        for i in 0.. {
            let target: String = format!("{}{}", self.line, i);
            let mut hasher = Md5::new();
            hasher.update(&target);
            if hasher.finalize().iter().take(3).all(|n| *n == 0) {
                let mut hasher = Md5::new();
                hasher.update(&target);
                let d = hasher
                    .finalize()
                    .iter()
                    .map(|n| format!("{:0>2x}", n))
                    .collect::<Vec<String>>()
                    .join("");
                dbg!(i, d);
                return i;
            }
        }
        0
    }
}
