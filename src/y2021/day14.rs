//! <https://adventofcode.com/2021/day/14>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::{HashMap, HashSet},
};

type Rule = (char, char, char);

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    template: Vec<char>,
    line: Vec<Rule>,
    rule: HashMap<(char, char), char>,
    atom: HashSet<char>,
}

mod parser {
    use {
        super::Rule,
        winnow::{
            ascii::{alpha1, newline},
            combinator::{separated, seq},
            token::one_of,
            ModalResult, Parser,
        },
    };

    fn parse_template(s: &mut &str) -> ModalResult<String> {
        alpha1.map(|s: &str| s.to_string()).parse_next(s)
    }

    fn parse_rule(s: &mut &str) -> ModalResult<Rule> {
        seq!(
        one_of('A'..='Z'),
        one_of('A'..='Z'),
        _: " -> ",
        one_of('A'..='Z')
        )
        .parse_next(s)
    }

    fn parse_rules(s: &mut &str) -> ModalResult<Vec<Rule>> {
        separated(1.., parse_rule, newline).parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<(String, Vec<Rule>)> {
        seq!(parse_template, _: (newline, newline), parse_rules).parse_next(s)
    }
}

#[aoc(2021, 14)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let (template, rules) = parser::parse(&mut input.as_str())?;
        self.template = template.chars().collect();
        self.line = rules.into_iter().collect();
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        for (l, r, m) in self.line.iter() {
            self.rule.insert((*l, *r), *m);
            self.atom.insert(*l);
            self.atom.insert(*r);
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut now = self.template.clone();
        for _ in 0..10 {
            let mut next: Vec<char> = Vec::new();
            for p in now.windows(2) {
                // println!("{:?}", p);
                next.push(p[0]);
                if let Some(ch) = self.rule.get(&(p[0], p[1])) {
                    next.push(*ch);
                }
            }
            next.push(*now.last().unwrap());
            std::mem::swap(&mut now, &mut next);
        }
        let occurs = self
            .atom
            .iter()
            .map(|c| now.iter().filter(|d| c == *d).count())
            .collect::<Vec<usize>>();
        // println!("{}", now.iter().collect::<String>());
        occurs.iter().max().unwrap() - occurs.iter().min().unwrap()
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut now: HashMap<(char, char), usize> = HashMap::new();
        for v in self.template.windows(2) {
            now.insert((v[0], v[1]), 1);
        }
        // add sentinel
        now.insert((self.template[self.template.len() - 1], ' '), 1);
        for _ in 0..40 {
            let mut next: HashMap<(char, char), usize> = HashMap::new();
            for (p, n) in now.iter() {
                // println!("{:?}", p);
                if let Some(m) = self.rule.get(&(p.0, p.1)) {
                    *next.entry((p.0, *m)).or_insert(0) += n;
                    *next.entry((*m, p.1)).or_insert(0) += n;
                } else {
                    next.insert(*p, *n);
                }
            }
            std::mem::swap(&mut now, &mut next);
        }
        let occurs = self
            .atom
            .iter()
            .map(|c| {
                now.iter()
                    .map(|(p, d)| if *c == p.0 { *d } else { 0 })
                    .sum()
            })
            .collect::<Vec<usize>>();
        occurs.iter().max().unwrap() - occurs.iter().min().unwrap()
    }
}
