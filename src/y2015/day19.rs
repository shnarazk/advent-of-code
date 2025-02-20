//! <https://adventofcode.com/2015/day/19>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    std::collections::{hash_map::Entry, HashMap, HashSet},
};

#[derive(Clone, Debug, Default)]
pub struct Puzzle {
    num_atom: usize,
    dic: HashMap<String, usize>,
    line: Vec<String>,
    rule: Vec<(String, Vec<String>)>,
}

mod parser {
    use winnow::{
        ascii::newline,
        combinator::{repeat, separated, seq},
        token::one_of,
        ModalResult, Parser,
    };

    fn parse_atom(s: &mut &str) -> ModalResult<String> {
        (
            one_of(|c: char| c.is_ascii_uppercase() || c == 'e'),
            repeat(0.., one_of(|c: char| c.is_ascii_lowercase())),
        )
            .map(|(c, v): (char, Vec<char>)| {
                let mut s = String::new();
                s.push(c);
                v.iter().for_each(|c| {
                    s.push(*c);
                });
                s
            })
            .parse_next(s)
    }

    fn parse_rule(s: &mut &str) -> ModalResult<(String, Vec<String>)> {
        seq!(parse_atom, _: " => ", repeat(1.., parse_atom)).parse_next(s)
    }

    #[allow(clippy::type_complexity)]
    pub fn parse(s: &mut &str) -> ModalResult<(Vec<(String, Vec<String>)>, Vec<String>)> {
        seq!(
            separated(1.., parse_rule, newline),
            _: "\n\n",
            repeat(1.., parse_atom)
        )
        .parse_next(s)
    }
}

#[aoc(2015, 19)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        let (rules, medicine) = parser::parse(&mut input.as_str())?;
        self.rule = rules;
        self.line = medicine;
        for (from, tos) in self.rule.iter() {
            if let Entry::Vacant(entry) = self.dic.entry(from.clone()) {
                entry.insert(self.num_atom);
                self.num_atom += 1;
            }
            for to in tos.iter() {
                if let Entry::Vacant(entry) = self.dic.entry(to.clone()) {
                    entry.insert(self.num_atom);
                    self.num_atom += 1;
                }
            }
        }
        Self::parsed()
    }
    fn end_of_data(&mut self) {
        self.dic.insert("e".to_string(), self.num_atom);
        self.num_atom += 1;
        // dbg!(&self.rule);
        // dbg!(&self.line);
        // dbg!(&self.dic);
        // coloring teminator
        // println!("- {}unique rule{}", color::RED, color::RESET);
        // println!("- {}without rule{}", color::BLUE, color::RESET);
        // for ch in self.line.iter() {
        //     match ch.as_str() {
        //         // unique
        //         "Si" | "Th" => print!("{}{}{}", color::RED, ch, color::RESET),
        //         // expandable
        //         "Al" | "B" | "Ca" | "F" | "H" | "Mg" | "N" | "O" | "P" | "Ti" | "e" => {
        //             print!("{}", ch)
        //         }
        //         // not expandable
        //         _ => print!("{}{}{}", color::BLUE, ch, color::RESET),
        //     }
        // }
        // println!();
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
        // for (i, (from, tos)) in self.rule.iter().enumerate().filter(|p| p.1 .0 != "e") {
        //     let target = tos.iter().cloned().collect::<String>();
        //     if rule2.iter().filter(|s| s.contains(&target)).count() == 2 * nrules - 1 {
        //         println!("{:>2}: {:>2} -> {:<11}", i, from, target);
        //     }
        // }
        let unique_terminators: Vec<(String, String)> = self
            .rule
            .iter()
            .filter(|p| p.0 != "e")
            .map(|(from, to)| (from.clone(), to.iter().cloned().collect::<String>()))
            .filter(|(_, target)| {
                rule2.iter().filter(|s| s.contains(target)).count() == 2 * nrules - 1
            })
            .collect::<Vec<_>>();
        // println!("{:?}", unique_terminators);
        let mut m: String = self.line.iter().cloned().collect::<String>();
        let mut counter = 0;
        for _ in 0..56 {
            for (from, pat) in unique_terminators.iter() {
                let c = counter;
                counter += (0..m.len()).filter(|i| m[*i..].starts_with(pat)).count();
                if c != counter {
                    // let p = re
                    //     .replace_all(&m, format!("{}{}{}", color::RED, pat, color::RESET))
                    //     .to_string();
                    // println!("{:>3};{:>8} => {:<2}: {}", counter, pat, from, p);
                    m = m.replace(pat, from);
                }
            }
        }
        // println!("212;     NAl => e : NAl");
        // println!("212;              : e");
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
        // for s in new_bag.iter() {
        //     println!(
        //         "{:?}",
        //         s.iter().map(|n| dic[*n]).collect::<Vec<&str>>().join("")
        //     );
        // }
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
                let c = counter;
                counter += (0..m.len()).filter(|i| m[*i..].starts_with(pat)).count();
                if c != counter {
                    // let p = re
                    //     .replace_all(&m, format!("{}{}{}", color::RED, pat, color::RESET))
                    //     .to_string();
                    // println!("{:>3};{:>8} => {:<2}: {}", counter, pat, from, p);
                    // m = re.replace_all(&m, from).to_string();
                    m = m.replace(pat, from);
                }
            }
        }
        // println!("212;     NAl => e : NAl");
        // println!("212;              : e");
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
