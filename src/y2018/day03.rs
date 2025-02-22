//! <https://adventofcode.com/2018/day/3>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::{HashMap, HashSet},
};

type Dim2 = (usize, usize);

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Claim {
    id: usize,
    left: usize,
    top: usize,
    width: usize,
    height: usize,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Puzzle {
    line: Vec<Claim>,
}

mod parser {
    use {
        super::*,
        crate::parser::parse_usize,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{separated, seq},
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Claim> {
        seq!(
            _: "#", parse_usize,
            _: " @ ", parse_usize,
            _: ",", parse_usize,
            _: ": ", parse_usize,
            _: "x", parse_usize,
        )
        .map(|(id, left, top, width, height)| Claim {
            id,
            left,
            top,
            width,
            height,
        })
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<Claim>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2018, 3)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.line = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut used: HashMap<Dim2, usize> = HashMap::new();
        for c in self.line.iter() {
            for j in (c.top..).take(c.height) {
                for i in (c.left..).take(c.width) {
                    *used.entry((j, i)).or_insert(0) += 1;
                }
            }
        }
        used.values().filter(|&&n| 1 < n).count()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut used: HashMap<Dim2, usize> = HashMap::new();
        let mut duplicated: HashSet<usize> = HashSet::new();
        for c in self.line.iter() {
            let mut dup = false;
            for j in (c.top..).take(c.height) {
                for i in (c.left..).take(c.width) {
                    if let Some(d) = used.get(&(j, i)) {
                        duplicated.insert(*d);
                        dup = true;
                    } else {
                        used.insert((j, i), c.id);
                    }
                }
            }
            if dup {
                duplicated.insert(c.id);
            }
        }
        for id in self.line.iter().map(|c| c.id) {
            if !duplicated.contains(&id) {
                return id;
            }
        }
        unreachable!();
    }
}
