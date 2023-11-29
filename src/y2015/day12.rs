//! <https://adventofcode.com/2015/day/12>
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        regex,
    },
    serde_json,
};

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<isize>>,
    raw: Vec<String>,
}

#[aoc_at(2015, 12)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        const PART1: bool = false;
        if PART1 {
            let non_digit = regex!(r"[^---0-9]+");
            let mut after = non_digit.replace_all(block, " ").to_string();
            after = after.trim().to_string();
            self.line.push(
                after
                    .split(' ')
                    .filter(|s| !s.is_empty())
                    .map(|s| {
                        if s.starts_with('-') {
                            -s.chars()
                                .skip(1)
                                .collect::<String>()
                                .parse::<isize>()
                                .unwrap()
                        } else {
                            s.parse::<isize>().unwrap()
                        }
                    })
                    .collect::<Vec<isize>>(),
            );
        } else {
            self.raw.push(block.to_string());
        }
        Ok(())
    }
    fn wrap_up(&mut self) {
        // dbg!(&self.line);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut num: isize = 0;
        for l in self.line.iter() {
            num = l.iter().sum::<isize>();
            println!("{}", num);
        }
        num
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut result: isize = 0;
        for l in self.raw.iter() {
            let obj: serde_json::Value = serde_json::from_str(l).expect("");
            result = collect(&obj);
            dbg!(result);
        }
        result
    }
}

fn collect(j: &serde_json::Value) -> isize {
    match j {
        serde_json::Value::Array(a) => a.iter().map(collect).sum::<isize>(),
        serde_json::Value::Number(n) => n.as_i64().unwrap() as isize,
        serde_json::Value::Object(map) if map.values().all(|k| k != "red") => {
            map.iter().map(|(_, v)| collect(v)).sum::<isize>()
        }
        _ => 0,
    }
}
