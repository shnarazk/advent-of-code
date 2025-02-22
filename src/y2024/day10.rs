//! <https://adventofcode.com/2024/day/10>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc},
        geometric::*,
        parser::parse_dec,
        rect::Rect,
    },
    serde::Serialize,
    std::collections::{HashMap, HashSet},
    winnow::{
        ModalResult, Parser,
        ascii::newline,
        combinator::{repeat, repeat_till},
    },
};

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Puzzle {
    line: Vec<Vec<usize>>,
    plane: Rect<usize>,
    heads: HashSet<Vec2>,
    size: Vec2,
}

impl Puzzle {
    fn aux1(
        &self,
        from: Vec2,
        lvl: usize,
        memo: &mut HashMap<Vec2, HashSet<Vec2>>,
    ) -> HashSet<Vec2> {
        if let Some(s) = memo.get(&from) {
            return s.clone();
        }
        let mut set: HashSet<Vec2> = HashSet::new();
        if lvl == 9 {
            set.insert(from);
        } else {
            from.neighbors4((0, 0), self.size).iter().for_each(|p| {
                let l = *self.plane.get(p).unwrap();
                if lvl + 1 == l {
                    let v = self.aux1(*p, l, memo);
                    for &q in v.iter() {
                        set.insert(q);
                    }
                }
            });
            memo.insert(from, set.clone());
        }
        set
    }
    fn count9_1(&self, from: Vec2, memo: &mut HashMap<Vec2, HashSet<Vec2>>) -> usize {
        self.aux1(from, 0, memo).len()
    }
    fn aux2(&self, from: Vec2, lvl: usize, memo: &mut Rect<Option<usize>>) -> usize {
        if let Some(Some(n)) = memo.get(from) {
            return *n;
        }
        if lvl == 9 {
            memo[&from] = Some(1);
            1
        } else {
            let mut count = 0;
            from.neighbors4((0, 0), self.size).iter().for_each(|p| {
                let l = *self.plane.get(p).unwrap();
                if lvl + 1 == l {
                    let x = self.aux2(*p, l, memo);
                    count += x;
                }
            });
            memo[&from] = Some(count);
            count
        }
    }
    fn count9_2(&self, from: Vec2, memo: &mut Rect<Option<usize>>) -> usize {
        self.aux2(from, 0, memo)
    }
}

fn parse_line(s: &mut &str) -> ModalResult<Vec<usize>> {
    let (v, _) = repeat_till(1.., parse_dec, newline).parse_next(s)?;
    Ok(v)
}

fn parse(s: &mut &str) -> ModalResult<Vec<Vec<usize>>> {
    repeat(1.., parse_line).parse_next(s)
}

#[aoc(2024, 10)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parse(&mut input)?;
        self.size.0 = self.line.len() as isize;
        self.size.1 = self.line[0].len() as isize;
        self.plane = Rect::new(self.size, 0);
        for (i, l) in self.line.iter().enumerate() {
            for (j, &n) in l.iter().enumerate() {
                self.plane[&(i as isize, j as isize)] = n;
                if n == 0 {
                    self.heads.insert((i as isize, j as isize));
                }
            }
        }
        Self::parsed()
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut memo: HashMap<Vec2, HashSet<Vec2>> = HashMap::new();
        self.heads
            .iter()
            .map(|&h| self.count9_1(h, &mut memo))
            .sum()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut memo: Rect<Option<usize>> = Rect::new(self.size, None);
        self.heads
            .iter()
            .map(|&h| self.count9_2(h, &mut memo))
            .sum()
    }
}
