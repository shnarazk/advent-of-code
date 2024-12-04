//! <https://adventofcode.com/2023/day/19>
use {
    crate::framework::{aoc, AdventOfCode, ParseError},
    itertools::Itertools,
    serde_json,
    std::collections::{HashMap, HashSet},
    winnow::{
        branch::alt,
        bytes::tag,
        character::{alpha1, dec_uint},
        multi::{many1, many_till0},
        sequence::{preceded, terminated},
        // stream::StreamIsPartial,
        IResult,
    },
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

fn parse_rule1(str: &str) -> IResult<&str, Rule> {
    let (remain1, var_str) = alpha1(str)?;
    let (remain2, op) = alt((tag("<"), tag(">")))(remain1)?;
    let (remain3, val): (&str, u64) = dec_uint(remain2)?;
    let (remain4, label) = preceded(tag(":"), alpha1)(remain3)?;
    let (remain5, _) = tag(",")(remain4)?;
    Ok((
        remain5,
        (
            Some((
                var_str.to_string(),
                if op == "<" { Op::Less } else { Op::Greater },
                val as usize,
            )),
            label.to_string(),
        ),
    ))
}

fn parse_workflow(str: &str) -> IResult<&str, (Label, Vec<Rule>)> {
    let (remain1, label) = terminated(alpha1, tag("{"))(str)?;
    let (remain2, (mut v, last_label)): (&str, (Vec<Rule>, &str)) =
        many_till0(parse_rule1, terminated(alpha1, tag("}\n")))(remain1)?;
    v.push((None, last_label.to_string()));
    Ok((remain2, (label.to_string(), v)))
}

fn parse_setting(str: &str) -> IResult<&str, Vec<(String, usize)>> {
    let (remain1, x): (&str, u64) = preceded(tag("{x="), dec_uint)(str)?;
    let (remain2, m): (&str, u64) = preceded(tag(",m="), dec_uint)(remain1)?;
    let (remain3, a): (&str, u64) = preceded(tag(",a="), dec_uint)(remain2)?;
    let (remain4, s): (&str, u64) = preceded(tag(",s="), dec_uint)(remain3)?;
    let (remain5, _) = tag("}\n")(remain4)?;
    Ok((
        remain5,
        vec![
            ("x".to_string(), x as usize),
            ("m".to_string(), m as usize),
            ("a".to_string(), a as usize),
            ("s".to_string(), s as usize),
        ],
    ))
}

#[aoc(2023, 19)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        #[allow(clippy::type_complexity)]
        let (remain1, (workflows, _)): (&str, (Vec<(Label, Vec<Rule>)>, &str)) =
            many_till0(parse_workflow, tag("\n"))(input.as_str())?;
        self.rules = workflows
            .iter()
            .cloned()
            .collect::<HashMap<Label, Vec<Rule>>>();
        for (_, rules) in self.rules.iter() {
            for rule in rules.iter() {
                if let Some((label, op, val)) = &rule.0 {
                    let var_index = match label.as_str() {
                        "x" => 0,
                        "m" => 1,
                        "a" => 2,
                        "s" => 3,
                        _ => unimplemented!(),
                    };
                    if Op::Less == *op {
                        self.rating_settings[var_index].insert(*val);
                    } else {
                        self.rating_settings[var_index].insert(*val + 1);
                    }
                }
            }
        }
        let (_, settings): (&str, Vec<Vec<(Label, usize)>>) = many1(parse_setting)(remain1)?;
        self.settings = settings
            .iter()
            .map(|v| v.iter().cloned().collect())
            .collect::<Vec<HashMap<Var, Val>>>();
        Ok("".to_string())
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
