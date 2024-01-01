//! <https://adventofcode.com/2023/day/19>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    itertools::Itertools,
    serde_json,
    std::collections::{HashMap, HashSet},
};

type Label = String;
type Var = String;
type Val = usize;
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Op {
    Less,
    Greater,
}

type Rule = (Option<(Var, Op, Val)>, Label);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    rules: HashMap<Label, Vec<Rule>>,
    settings: Vec<HashMap<Var, Val>>,
    reading_settings: bool,
    rating_settings: [HashSet<usize>; 4],
}

#[aoc(2023, 19)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "\n";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let rule_parser = regex!(r"^([A-Za-z]+)\{(.+)\}$");
        let assign_parser = regex!(r"^\{(.+)\}$");
        if let Some(segment) = rule_parser.captures(block) {
            let name = segment[1].to_string();
            let v = segment[2]
                .split(',')
                .map(|pat| {
                    if pat.contains(':') {
                        let cond_and_label = pat.split(':').collect::<Vec<_>>();
                        let parser2 = regex!(r"^([A-Za-z]+)(>|<)(\d+)$");
                        let cov = parser2.captures(cond_and_label[0]).unwrap();
                        let var: Var = cov[1].to_string();
                        let var_index = match &cov[1] {
                            "x" => 0,
                            "m" => 1,
                            "a" => 2,
                            "s" => 3,
                            _ => unimplemented!(),
                        };
                        let val = cov[3].parse::<usize>().unwrap();
                        let op: Op = match &cov[2] {
                            "<" => {
                                self.rating_settings[var_index].insert(val);
                                Op::Less
                            }
                            ">" => {
                                self.rating_settings[var_index].insert(val + 1);
                                Op::Greater
                            }
                            _ => unreachable!(),
                        };
                        let label = cond_and_label[1].to_string();
                        (Some((var, op, val)), label)
                    } else {
                        let label = pat.to_string();
                        (None, label)
                    }
                })
                .collect::<Vec<_>>();
            self.rules.insert(name, v);
        } else if let Some(segment) = assign_parser.captures(block) {
            let v = segment[1]
                .split(',')
                .map(|a| {
                    let exp = a.split('=').collect::<Vec<_>>();
                    (exp[0].to_string(), exp[1].parse::<usize>().unwrap())
                })
                .collect::<HashMap<_, _>>();
            self.settings.push(v);
        } else {
            panic!();
        }
        Ok(())
    }
    fn end_of_data(&mut self) {
        for i in 0..4 {
            let mut it = self.rating_settings[i].iter().sorted();
            let beg = *it.next().unwrap();
            let end = *it.last().unwrap();
            if 1 < beg {
                self.rating_settings[i].insert(1);
            }
            if end < 4001 {
                self.rating_settings[i].insert(4001);
            }
        }
    }
    fn serialize(&self) -> Option<String> {
        serde_json::to_string(
            &self
                .rules
                .iter()
                .flat_map(|(from, rules)| {
                    rules
                        .iter()
                        .filter(|(_, to)| !["A", "R"].contains(&to.as_str()))
                        .map(|(_, to)| (from, to))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>(),
        )
        .ok()
    }
    fn part1(&mut self) -> Self::Output1 {
        self.settings
            .iter()
            .filter(|setting| self.check(setting))
            .map(|setting| setting.values().sum::<usize>())
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        self.gather_positives(
            &"in".to_string(),
            vec![(1, 4000), (1, 4000), (1, 4000), (1, 4000)],
        )
    }
}

impl Puzzle {
    fn execute(&self, setting: &HashMap<Var, Val>, label: &Label) -> bool {
        match label.as_str() {
            "A" => return true,
            "R" => return false,
            _ => (),
        }
        let Some(rules) = self.rules.get(label) else {
            panic!();
        };
        for (cond, lbl) in rules {
            if let Some((var, op, val)) = cond {
                let Some(var_val) = setting.get(var) else {
                    unreachable!();
                };
                let exp = match op {
                    Op::Less => var_val < val,
                    Op::Greater => var_val > val,
                };
                if exp {
                    return self.execute(setting, lbl);
                }
            } else {
                return self.execute(setting, lbl);
            }
        }
        false
    }
    fn check(&self, setting: &HashMap<Var, Val>) -> bool {
        self.execute(setting, &"in".to_string())
    }
    fn gather_positives(&self, node: &Label, mut constraints: Vec<(usize, usize)>) -> usize {
        let mut total: usize = 0;
        if node == "A" {
            return constraints
                .iter()
                .map(|(b, e)| *e - *b + 1)
                .product::<usize>();
        }
        if node == "R" {
            return 0;
        }
        for (condition, dest) in self.rules.get(node).unwrap() {
            if let Some((var, op, val)) = condition {
                let index = ["x", "m", "a", "s"]
                    .iter()
                    .enumerate()
                    .find(|(_, v)| **v == var.as_str())
                    .unwrap()
                    .0;
                let mut cons = constraints.clone();
                match op {
                    Op::Less if *val <= constraints[index].0 => {
                        continue;
                    }
                    Op::Less => {
                        cons[index].1 = cons[index].1.min(*val - 1);
                        constraints[index].0 = constraints[index].0.max(*val);
                    }
                    Op::Greater if constraints[index].1 <= *val => {
                        continue;
                    }
                    Op::Greater => {
                        cons[index].0 = cons[index].0.max(*val + 1);
                        constraints[index].1 = constraints[index].1.min(*val);
                    }
                }
                total += self.gather_positives(dest, cons);
            } else {
                total += self.gather_positives(dest, constraints.clone());
            }
        }
        total
    }
}
