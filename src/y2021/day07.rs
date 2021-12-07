use crate::{AdventOfCode, Description, ParseError, TryParse};

type DataSegment = Vec<usize>;

impl TryParse for DataSegment {
    fn parse(s: &str) -> Result<Self, ParseError> {
        Ok(s.trim()
            .split(',')
            .map(|i| i.parse::<usize>().unwrap())
            .collect())
    }
}

#[derive(Debug, PartialEq)]
struct Puzzle {
    line: DataSegment,
}

impl AdventOfCode for Puzzle {
    type Segment = DataSegment;
    type Output1 = usize;
    type Output2 = usize;
    const YEAR: usize = 2021;
    const DAY: usize = 7;
    const DELIMITER: &'static str = "\n";
    fn default() -> Self {
        Self { line: Vec::new() }
    }
    fn insert(&mut self, object: Self::Segment) {
        self.line = object;
    }
    fn part1(&mut self) -> usize {
        let vec = &self.line;
        let len: usize = *vec.iter().max().unwrap();
        let mut fmin: usize = vec.iter().sum::<usize>().pow(2);
        for pos in 0..=len {
            fmin = fmin.min(
                vec.iter()
                    .map(|i| (*i as isize - pos as isize).abs() as usize)
                    .sum(),
            );
        }
        fmin
    }
    fn part2(&mut self) -> usize {
        let vec = &self.line;
        let len: usize = *vec.iter().max().unwrap();
        let mut fuel_table: Vec<Option<usize>> = Vec::new();
        fuel_table.resize(len + 1, None);
        fuel_table[0] = Some(0);
        fn get(table: &mut Vec<Option<usize>>, n: usize) -> usize {
            if let Some(k) = table[n] {
                k
            } else {
                let v = n + get(table, n - 1);
                table[n] = Some(v);
                v
            }
        }
        let mut fmin: usize = vec.iter().sum::<usize>().pow(2);
        for pos in 0..=len {
            fmin = fmin.min(
                vec.iter()
                    .map(|i| get(&mut fuel_table, (*i as isize - pos as isize).abs() as usize))
                    .sum(),
            );
        }
        fmin
    }
}

pub fn go(part: usize, desc: Description) {
    dbg!(Puzzle::solve(&desc, part));
}

