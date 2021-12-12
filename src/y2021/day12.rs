use {
    crate::framework::{aoc_at, AdventOfCode, Maybe, ParseError},
    lazy_static::lazy_static,
    regex::Regex,
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

#[derive(Debug, Default)]
pub struct Puzzle {
    line: Vec<(Node, Node)>,
    path: HashSet<(Node, Node)>,
}

impl Puzzle {
    fn count_to(&self, path: Vec<&Node>) -> usize {
        let here: &Node = *path.last().unwrap();
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
        let here: &Node = *path.last().unwrap();
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

#[aoc_at(2021, 12)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Maybe<()> {
        lazy_static! {
            static ref PARSER: Regex =
                Regex::new(r"^(start|end|[a-z]+|[A-Z]+)-(start|end|[a-z]+|[A-Z]+)$")
                    .expect("wrong");
        }
        // dbg!(&block);
        let segment = PARSER.captures(block).ok_or(ParseError)?;
        let b: Node = match &segment[1] {
            "start" => Node::Start,
            "end" => Node::End,
            s if s.chars().all(|c| c.is_ascii_lowercase()) => Node::Small(s.to_string()),
            b => Node::Big(b.to_string()),
        };
        let e: Node = match &segment[2] {
            "start" => Node::Start,
            "end" => Node::End,
            s if s.chars().all(|c| c.is_ascii_lowercase()) => Node::Small(s.to_string()),
            b => Node::Big(b.to_string()),
        };
        self.line.push((b, e));
        Ok(())
    }
    fn after_insert(&mut self) {
        for (from, to) in self.line.iter() {
            self.path.insert((from.clone(), to.clone()));
            self.path.insert((to.clone(), from.clone()));
        }
        dbg!(self.path.len());
    }
    fn part1(&mut self) -> Self::Output1 {
        self.count_to(vec![&Node::End])
    }
    fn part2(&mut self) -> Self::Output2 {
        self.count_to(vec![&Node::End]) + self.count_to2(vec![&Node::End], None)
    }
}
