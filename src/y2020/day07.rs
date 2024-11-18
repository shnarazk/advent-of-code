//! <https://adventofcode.com/2020/day/7>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::collections::HashSet,
};

#[derive(Eq, Debug, Hash, PartialEq)]
struct Link {
    outer: String,
    inner: String,
    amount: usize,
}

#[derive(Debug, Default, PartialEq)]
pub struct Puzzle {
    links: HashSet<Link>,
}

#[aoc(2020, 7)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let head = regex!(r"^([a-z]+ [a-z]+) bags? contain (.*)");
        let prep = regex!(r"(\d+) ([a-z]+ [a-z]+) bags?(, (.*))?");
        if let Some(head) = head.captures(block) {
            let mut b: String = head[2].to_string();
            while let Some(prep) = prep.captures(&b) {
                self.links.insert(Link {
                    outer: head[1].to_string(),
                    inner: prep[2].to_string(),
                    amount: prep[1].parse::<usize>().unwrap(),
                });
                if let Some(rest) = prep.get(4) {
                    b = rest.as_str().to_string();
                    if b == "." {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
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
