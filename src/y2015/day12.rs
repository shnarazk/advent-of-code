//! <https://adventofcode.com/2015/day/12>
use {
    crate::framework::{aoc_at, AdventOfCode, ParseError},
    serde_json,
};

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Vec<isize>>,
    raw: Vec<String>,
}

#[aoc_at(2015, 12)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    fn parse(&mut self, s: String) -> Result<String, ParseError> {
        for l in s.lines() {
            let mut after = l
                .chars()
                .map(|c| {
                    if c == '-' || c.is_ascii_digit() {
                        c
                    } else {
                        ' '
                    }
                })
                .collect::<String>();
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
            self.raw.push(l.to_string());
        }
        Self::parsed()
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
