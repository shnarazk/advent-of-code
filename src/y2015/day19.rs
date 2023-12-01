//! <https://adventofcode.com/2015/day/19>
use {
    crate::{
        color,
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    regex::Regex,
    std::collections::HashMap,
    std::collections::HashSet,
};

#[derive(Debug, Default)]
pub struct Puzzle {
    num_atom: usize,
    dic: HashMap<String, usize>,
    line: Vec<String>,
    rule: Vec<(String, Vec<String>)>,
}

fn parse_atoms(mut stream: Vec<String>, line: &str) -> Vec<String> {
    let atom = regex!(r"^([A-Z][^A-Z]*)(.*)$");
    if let Some(segment) = atom.captures(line) {
        stream.push(segment[1].to_string());
        return parse_atoms(stream, &segment[2]);
    }
    stream
}

#[aoc(2015, 19)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let rule = regex!(r"^([A-Z][a-zA-Z]*) => ([A-Z][a-zA-Z]*)$");
        let bigbang = regex!(r"^e => ([A-Z][a-zA-Z]*)$");
        let string = regex!(r"^([A-Z][a-zA-Z]+)$");
        if let Some(segment) = rule.captures(block) {
            let prec = parse_atoms(Vec::new(), &segment[1]);
            let post = parse_atoms(Vec::new(), &segment[2]);
            assert!(prec.len() == 1, "{:?}", prec);
            for w in prec.iter() {
                if !self.dic.contains_key(w) {
                    self.dic.insert(w.to_string(), self.num_atom);
                    self.num_atom += 1;
                }
            }
            for w in post.iter() {
                if !self.dic.contains_key(w) {
                    self.dic.insert(w.to_string(), self.num_atom);
                    self.num_atom += 1;
                }
            }
            self.rule.push((prec[0].to_string(), post));
        } else if let Some(segment) = bigbang.captures(block) {
            let post = parse_atoms(Vec::new(), &segment[1]);
            for w in post.iter() {
                if !self.dic.contains_key(w) {
                    self.dic.insert(w.to_string(), self.num_atom);
                    self.num_atom += 1;
                }
            }
            self.rule.push(("e".to_string(), post));
        } else if let Some(segment) = string.captures(block) {
            let string = parse_atoms(Vec::new(), &segment[0]);
            for w in string.iter() {
                if !self.dic.contains_key(w) {
                    self.dic.insert(w.to_string(), self.num_atom);
                    self.num_atom += 1;
                }
            }
            self.line = string;
        }
        Ok(())
    }
    fn end_of_data(&mut self) {
        self.dic.insert("e".to_string(), self.num_atom);
        self.num_atom += 1;
        // dbg!(&self.rule);
        // dbg!(&self.line);
        // dbg!(&self.dic);
        // coloring teminator
        println!("- {}unique rule{}", color::RED, color::RESET);
        println!("- {}without rule{}", color::BLUE, color::RESET);
        for ch in self.line.iter() {
            match ch.as_str() {
                // unique
                "Si" | "Th" => print!("{}{}{}", color::RED, ch, color::RESET),
                // expandable
                "Al" | "B" | "Ca" | "F" | "H" | "Mg" | "N" | "O" | "P" | "Ti" | "e" => {
                    print!("{}", ch)
                }
                // not expandable
                _ => print!("{}{}{}", color::BLUE, ch, color::RESET),
            }
        }
        println!();
        // make all combination of pairs
        let nrules = self.rule.iter().filter(|(from, _)| *from != "e").count();
        let rule2: Vec<String> = self
            .rule
            .iter()
            .filter(|(from, _)| *from != "e")
            .map(|(_, chs)| chs.iter().cloned().collect::<String>())
            .flat_map(|to1| {
                self.rule
                    .iter()
                    .filter(|(from, _)| *from != "e")
                    .map(|(_, chs)| chs.iter().cloned().collect::<String>())
                    .map(|to2| format!("{}{}", to1, to2))
                    .collect::<Vec<String>>()
            })
            .collect::<Vec<String>>();
        assert_eq!(rule2.len(), nrules * nrules);
        for (i, (from, tos)) in self.rule.iter().enumerate().filter(|p| p.1 .0 != "e") {
            let target = tos.iter().cloned().collect::<String>();
            if rule2.iter().filter(|s| s.contains(&target)).count() == 2 * nrules - 1 {
                println!("{:>2}: {:>2} -> {:<11}", i, from, target);
            }
        }
        let unique_terminators: Vec<(String, String)> = self
            .rule
            .iter()
            .filter(|p| p.0 != "e")
            .map(|(from, to)| (from.clone(), to.iter().cloned().collect::<String>()))
            .filter(|(_, target)| {
                rule2.iter().filter(|s| s.contains(target)).count() == 2 * nrules - 1
            })
            .collect::<Vec<_>>();
        println!("{:?}", unique_terminators);
        let mut m: String = self.line.iter().cloned().collect::<String>();
        let mut counter = 0;
        for _ in 0..56 {
            for (from, pat) in unique_terminators.iter() {
                let re = Regex::new(pat).unwrap();
                let c = counter;
                counter += (0..m.len()).filter(|i| m[*i..].starts_with(pat)).count();
                if c != counter {
                    let p = re
                        .replace_all(&m, format!("{}{}{}", color::RED, pat, color::RESET))
                        .to_string();
                    println!("{:>3};{:>8} => {:<2}: {}", counter, pat, from, p);
                    m = re.replace_all(&m, from).to_string();
                }
            }
        }
        println!("212;     NAl => e : NAl");
        println!("212;              : e");
    }
    fn part1(&mut self) -> Self::Output1 {
        // dbg!(&self.rule);
        let mut dic = Vec::new();
        dic.resize(self.num_atom, "");
        for (w, n) in self.dic.iter() {
            dic[*n] = w;
        }
        let rule = self
            .rule
            .iter()
            .map(|(atom, a)| {
                (
                    *self.dic.get(atom).unwrap(),
                    a.iter()
                        .map(|atom| *self.dic.get(atom).unwrap())
                        .collect::<Vec<usize>>(),
                )
            })
            .collect::<Vec<(usize, Vec<usize>)>>();
        let string = self
            .line
            .iter()
            .map(|s| *self.dic.get(s).unwrap())
            .collect::<Vec<usize>>();
        let mut bag: HashSet<Vec<usize>> = HashSet::new();
        bag.insert(string);
        let mut new_bag: HashSet<Vec<usize>> = HashSet::new();
        for st in bag.iter() {
            for (i, n) in st.iter().enumerate() {
                for (_, seq) in rule.iter().filter(|(key, _)| key == n) {
                    let mut new_string: Vec<usize> = st.clone();
                    new_string.remove(i);
                    for x in seq.iter().rev() {
                        new_string.insert(i, *x);
                    }
                    new_bag.insert(new_string);
                }
            }
        }
        for s in new_bag.iter() {
            println!(
                "{:?}",
                s.iter().map(|n| dic[*n]).collect::<Vec<&str>>().join("")
            );
        }
        new_bag.len()
    }
    fn part2(&mut self) -> Self::Output2 {
        // make all combination of pairs
        let nrules = self.rule.iter().filter(|(from, _)| *from != "e").count();
        let rule2: Vec<String> = self
            .rule
            .iter()
            .filter(|(from, _)| *from != "e")
            .map(|(_, chs)| chs.iter().cloned().collect::<String>())
            .flat_map(|to1| {
                self.rule
                    .iter()
                    .filter(|(from, _)| *from != "e")
                    .map(|(_, chs)| chs.iter().cloned().collect::<String>())
                    .map(|to2| format!("{}{}", to1, to2))
                    .collect::<Vec<String>>()
            })
            .collect::<Vec<String>>();
        assert_eq!(rule2.len(), nrules * nrules);
        let unique_terminators: Vec<(String, String)> = self
            .rule
            .iter()
            .filter(|p| p.0 != "e")
            .map(|(from, to)| (from.clone(), to.iter().cloned().collect::<String>()))
            .filter(|(_, target)| {
                rule2.iter().filter(|s| s.contains(target)).count() == 2 * nrules - 1
            })
            .collect::<Vec<_>>();
        let mut m: String = self.line.iter().cloned().collect::<String>();
        let mut counter = 0;
        for _ in 0..56 {
            for (from, pat) in unique_terminators.iter() {
                let re = Regex::new(pat).unwrap();
                let c = counter;
                counter += (0..m.len()).filter(|i| m[*i..].starts_with(pat)).count();
                if c != counter {
                    let p = re
                        .replace_all(&m, format!("{}{}{}", color::RED, pat, color::RESET))
                        .to_string();
                    println!("{:>3};{:>8} => {:<2}: {}", counter, pat, from, p);
                    m = re.replace_all(&m, from).to_string();
                }
            }
        }
        println!("212;     NAl => e : NAl");
        println!("212;              : e");
        counter + 1
    }
}

impl Puzzle {
    #[allow(dead_code)]
    fn part2_not_work(&mut self) -> usize {
        // self.dic.insert("e".to_string(), self.num_atom);
        dbg!(self.line.len());
        dbg!(&self.rule.len());
        let mut to_mnemonic = Vec::new();
        to_mnemonic.resize(self.num_atom + 1, "");
        for (w, n) in self.dic.iter() {
            to_mnemonic[*n] = w;
        }
        let rule = self
            .rule
            .iter()
            .map(|(atom, a)| {
                (
                    *self.dic.get(atom).unwrap(),
                    a.iter()
                        .map(|atom| *self.dic.get(atom).unwrap())
                        .collect::<Vec<usize>>(),
                )
            })
            .collect::<Vec<(usize, Vec<usize>)>>();
        let medicine = self
            .line
            .iter()
            .map(|s| *self.dic.get(s).unwrap())
            .collect::<Vec<usize>>();
        dbg!((0..medicine.len())
            .filter(|i| rule.iter().any(|(atom, _)| medicine[*i] == *atom))
            .count());
        let mut bag: HashSet<Vec<usize>> = HashSet::new();
        let mut new_bag: HashSet<Vec<usize>> = HashSet::new();
        bag.insert(vec![0]);
        for _ in 1.. {
            for st in bag.iter() {
                for (i, n) in st.iter().enumerate() {
                    for (_, seq) in rule.iter().filter(|(key, _)| key == n) {
                        let mut new_string: Vec<usize> = st.clone();
                        new_string.remove(i);
                        for x in seq.iter().rev() {
                            new_string.insert(i, *x);
                        }
                        if new_string.starts_with(&medicine) {
                            dbg!(new_string
                                .iter()
                                .map(|n| to_mnemonic[*n])
                                .collect::<Vec<&str>>()
                                .join(""));
                            return i;
                        }
                        if new_string.len() < medicine.len() {
                            new_bag.insert(new_string);
                        }
                    }
                }
            }
            std::mem::swap(&mut bag, &mut new_bag);
            new_bag.clear();
        }
        for s in new_bag.iter() {
            println!(
                "{:?}",
                s.iter()
                    .map(|n| to_mnemonic[*n])
                    .collect::<Vec<&str>>()
                    .join("")
            );
        }
        new_bag.len()
    }
}
