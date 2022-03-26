//! <https://adventofcode.com/2015/day/13>
use {
    crate::{
        framework::{aoc_at, AdventOfCode, ParseError},
        regex,
    },
    itertools::Itertools,
    std::collections::{HashMap, HashSet},
};

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    person: HashSet<String>,
    line: Vec<(String, String, isize)>,
}

#[aoc_at(2015, 13)]
impl AdventOfCode for Puzzle {
    type Output1 = isize;
    type Output2 = isize;
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let parser = regex!(
            r"^([A-Z][a-z]+) would (gain|lose) ([0-9]+) happiness units by sitting next to ([A-Z][a-z]+)\.$"
        );
        let segment = parser.captures(block).ok_or(ParseError)?;
        self.line.push((
            segment[1].to_string(),
            segment[4].to_string(),
            if &segment[2] == "gain" {
                segment[3].parse::<isize>()?
            } else {
                -segment[3].parse::<isize>()?
            },
        ));
        Ok(())
    }
    fn after_insert(&mut self) {
        for (p1, p2, _) in self.line.iter() {
            self.person.insert(p1.to_string());
            self.person.insert(p2.to_string());
        }
        dbg!(&self.person);
    }
    fn part1(&mut self) -> Self::Output1 {
        let mut likes: HashMap<(&str, &str), isize> = HashMap::new();
        for (p1, p2, v) in self.line.iter() {
            likes.insert((p1, p2), *v);
        }
        let person: Vec<&String> = self.person.iter().collect::<Vec<&String>>();
        let n = person.len();
        let mut max_happiness: isize = 0;
        for pos in (0..n).permutations(n) {
            let mut happiness: isize = 0;
            // pos[n - 1] - pos[0] - pos[1]
            println!(
                "{} - {} - {}",
                &person[pos[n - 1]],
                &person[pos[0]],
                &person[pos[1]],
            );
            happiness += likes.get(&(person[pos[0]], person[pos[n - 1]])).unwrap();
            happiness += likes.get(&(person[pos[0]], person[pos[1]])).unwrap();
            for p in pos.windows(3) {
                println!("{} - {} - {}", &person[p[0]], &person[p[1]], &person[p[2]],);
                happiness += likes.get(&(person[p[1]], person[p[0]])).unwrap();
                happiness += likes.get(&(person[p[1]], person[p[2]])).unwrap();
            }
            // pos[n - 2] - pos[n-1] - pos[0]
            println!(
                "{} - {} - {}",
                &person[pos[n - 2]],
                &person[pos[n - 1]],
                &person[pos[0]],
            );
            happiness += likes
                .get(&(person[pos[n - 1]], person[pos[n - 2]]))
                .unwrap();
            happiness += likes.get(&(person[pos[n - 1]], person[pos[0]])).unwrap();
            println!();
            max_happiness = max_happiness.max(happiness);
        }
        max_happiness
    }
    fn part2(&mut self) -> Self::Output2 {
        let mut likes: HashMap<(&str, &str), isize> = HashMap::new();
        for (p1, p2, v) in self.line.iter() {
            likes.insert((p1, p2), *v);
        }
        let mut person: Vec<&String> = self.person.iter().collect::<Vec<&String>>();
        let me = "ME".to_string();
        person.push(&me);
        let n = person.len();
        let mut max_happiness: isize = 0;
        for pos in (0..n).permutations(n) {
            let mut happiness: isize = 0;
            // pos[n - 1] - pos[0] - pos[1]
            happiness += likes
                .get(&(person[pos[0]], person[pos[n - 1]]))
                .unwrap_or(&0);
            happiness += likes.get(&(person[pos[0]], person[pos[1]])).unwrap_or(&0);
            for p in pos.windows(3) {
                happiness += likes.get(&(person[p[1]], person[p[0]])).unwrap_or(&0);
                happiness += likes.get(&(person[p[1]], person[p[2]])).unwrap_or(&0);
            }
            // pos[n - 2] - pos[n-1] - pos[0]
            happiness += likes
                .get(&(person[pos[n - 1]], person[pos[n - 2]]))
                .unwrap_or(&0);
            happiness += likes
                .get(&(person[pos[n - 1]], person[pos[0]]))
                .unwrap_or(&0);
            max_happiness = max_happiness.max(happiness);
        }
        // optimize1(self.person.clone(), &self.likes);
        max_happiness
    }
}
