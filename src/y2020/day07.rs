//! <https://adventofcode.com/2020/day/7>
use {
    crate::framework::{AdventOfCode, ParseError, aoc},
    std::collections::HashSet,
};

#[derive(Clone, Eq, Debug, Hash, PartialEq)]
struct Link {
    outer: String,
    inner: String,
    amount: usize,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    links: HashSet<Link>,
}

mod parser {
    use {
        super::Link,
        crate::parser::parse_usize,
        std::collections::HashSet,
        winnow::{
            ModalResult, Parser,
            ascii::newline,
            combinator::{alt, opt, separated, seq},
            token::take_until,
        },
    };

    fn parse_line(s: &mut &str) -> ModalResult<Vec<Link>> {
        seq!(
            take_until(1.., " bags").map(|s: &str| s.to_string()),
            _: " bags contain ",
            alt((
                separated(1..,
                    seq!(
                        parse_usize,
                        _: " ",
                        take_until(1.., " bag").map(|s : &str| s.to_string()),
                        _: " bag",
                        _: opt("s")
                    ),
                    ", "
                ),
                "no other bags".map(|_| Vec::new())
            )),
            _: "."
        )
        .map(|(outer, inners)| {
            inners
                .into_iter()
                .map(|(amount, inner)| Link {
                    outer: outer.clone(),
                    inner,
                    amount,
                })
                .collect()
        })
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<HashSet<Link>> {
        separated(1.., parse_line, newline)
            .map(|v: Vec<Vec<Link>>| v.into_iter().flatten().collect::<HashSet<Link>>())
            .parse_next(s)
    }
}

#[aoc(2020, 7)]
impl AdventOfCode for Puzzle {
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        self.links = parser::parse(&mut input)?;
        Ok(())
    }
    fn part1(&mut self) -> usize {
        let mut outers: HashSet<String> = HashSet::new();
        most_outer_of(&self.links, "shiny gold", &mut outers);
        outers.len()
    }
    fn part2(&mut self) -> usize {
        let mut outers: HashSet<String> = HashSet::new();
        most_outer_of(&self.links, "shiny gold", &mut outers);
        collects(&self.links, "shiny gold") - 1
    }
}

fn most_outer_of(links: &HashSet<Link>, origin: &str, outers: &mut HashSet<String>) {
    for link in links {
        if link.inner == origin {
            outers.insert(link.outer.to_string());
            most_outer_of(links, &link.outer, outers);
        }
    }
}

fn collects(links: &HashSet<Link>, origin: &str) -> usize {
    let mut count = 0;
    for link in links {
        if link.outer == origin {
            count += link.amount * collects(links, &link.inner);
        }
    }
    count + 1
}
