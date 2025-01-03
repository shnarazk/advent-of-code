//! <https://adventofcode.com/2021/day/12>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::HashSet,
};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum Node {
    Start,
    End,
    Big(String),
    Small(String),
}

impl Node {
    fn is_big(&self) -> bool {
        matches!(self, Node::Big(_))
    }
    fn is_small(&self) -> bool {
        matches!(self, Node::Small(_))
    }
}

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    line: Vec<(Node, Node)>,
    path: HashSet<(Node, Node)>,
}

impl Puzzle {
    fn count_to(&self, path: Vec<&Node>) -> usize {
        let here: &Node = path.last().unwrap();
        if *here == Node::Start {
            let mut p = path.clone();
            p.reverse();
            // println!("{:?}", p);
            return 1;
        }
        let mut count = 0;
        for (_, to) in self.path.iter().filter(|(from, _)| *from == *here) {
            if !to.is_big() && path.contains(&to) {
                continue;
            }
            let mut cand = path.clone();
            cand.push(to);
            count += self.count_to(cand);
        }
        count
    }
    fn count_to2(&self, path: Vec<&Node>, favorite: Option<&Node>) -> usize {
        let here: &Node = path.last().unwrap();
        if *here == Node::Start {
            if let Some(f) = favorite {
                if path.iter().filter(|n| **n == f).count() == 2 {
                    // let mut p = path.clone();
                    // p.reverse();
                    // println!("{:?} -- {:?}", p, f);
                    return 1;
                }
            }
            return 0;
        }
        let mut count = 0;
        for (_, to) in self.path.iter().filter(|(from, _)| *from == *here) {
            match to {
                Node::End => continue,
                Node::Small(_) if favorite == Some(to) => {
                    if path.iter().filter(|n| *n == &to).count() == 2 {
                        continue;
                    }
                }
                Node::Small(_) if path.contains(&to) => continue,
                _ => (),
            }
            let mut cand = path.clone();
            cand.push(to);
            if favorite.is_none() && to.is_small() {
                count += self.count_to2(cand.clone(), Some(to));
            }
            count += self.count_to2(cand, favorite);
        }
        count
    }
}

mod parser {
    use {
        super::Node,
        winnow::{
            ascii::newline,
            combinator::{alt, repeat, separated, seq},
            token::one_of,
            PResult, Parser,
        },
    };

    fn parse_node(s: &mut &str) -> PResult<Node> {
        alt((
            "start".map(|_| Node::Start),
            "end".map(|_| Node::End),
            repeat(1.., one_of('A'..='Z')).map(Node::Big),
            repeat(1.., one_of('a'..='z')).map(Node::Small),
        ))
        .parse_next(s)
    }
    fn parse_line(s: &mut &str) -> PResult<(Node, Node)> {
        seq!((parse_node, _: "-", parse_node)).parse_next(s)
    }

    pub fn parse(s: &mut &str) -> PResult<Vec<(Node, Node)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc(2021, 12)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parser::parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for (from, to) in self.line.iter() {
            self.path.insert((from.clone(), to.clone()));
            self.path.insert((to.clone(), from.clone()));
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        self.count_to(vec![&Node::End])
    }
    fn part2(&mut self) -> Self::Output2 {
        self.count_to(vec![&Node::End]) + self.count_to2(vec![&Node::End], None)
    }
}
