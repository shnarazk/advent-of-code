//! <https://adventofcode.com/2020/day/21>
use {
    crate::{
        framework::{AdventOfCode, ParseError, aoc_at},
        progress,
    },
    splr::*,
    std::{
        collections::{HashMap, HashSet},
        convert::TryFrom,
    },
};

#[derive(Clone, Debug, Default, PartialEq)]
struct Rule {
    ingredients: Vec<String>,
    allergens: Vec<String>,
}

/// ## 変数
/// ingredient x allergen
///
/// ## ルール
/// 1. \[ONLY-ONE-AllERGEN\] ある ingredient がある allergen を持つなら他の indredient はその allergen を持てない
/// 1. \[EXCULSIZE-ALLERGEN\] ある ingredient がある allergen を持つなら他の allergen を持てない
/// 1. \[AT-LEAST-1\] ルールに則して、どれかはそのallergen を持たなければならない
/// 1. \[XOR\] ある ingredient がある allergen を持つなら他の ingredient はその allergen を持てない
/// 1. allergenに対して候補がある
///
/// * {mxmxvkd.dairy, kfcds.dairy, sqjhc.dairy, nhms.dairy}
/// * {mxmxvkd.dairy, kfcds.fish, sqjhc.fish, nhms.fish}
/// * {trh.dairy, fvjkl.dairy, sbzzf.dairy, mxmxvkd.dairy}
/// * ...
///
/// ## 目的
/// どの属性でもtrueにしたらUNSATになるようなindredientを探せ
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Puzzle {
    ingredients: HashMap<String, usize>,
    allergens: HashMap<String, usize>,
    rules: Vec<Rule>,
}

mod parser {
    use winnow::{
        ModalResult, Parser,
        ascii::{alpha1, newline},
        combinator::{separated, seq},
    };

    fn parse_line(s: &mut &str) -> ModalResult<(Vec<String>, Vec<String>)> {
        seq!(
            separated(1.., alpha1, " "),
            _: " (contains ",
            separated(1.., alpha1, ", "),
            _: ")"
        )
        .map(|(s, v): (Vec<&str>, Vec<&str>)| {
            (
                s.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
                v.iter().map(|s| s.to_string()).collect(),
            )
        })
        .parse_next(s)
    }

    pub fn parse(s: &mut &str) -> ModalResult<Vec<(Vec<String>, Vec<String>)>> {
        separated(1.., parse_line, newline).parse_next(s)
    }
}

#[aoc_at(2020, 21)]
impl AdventOfCode for Puzzle {
    type Output1 = usize;
    type Output2 = String;
    fn prepare(&mut self, mut input: &str) -> Result<(), ParseError> {
        let data = parser::parse(&mut input)?;
        for (ingredients, allergens) in data {
            let mut num_ingredient = self.ingredients.len();
            for ing in ingredients.iter() {
                if !self.ingredients.contains_key(ing) {
                    self.ingredients.insert(ing.to_string(), num_ingredient);
                    num_ingredient += 1;
                }
            }
            let mut num_allergen = self.allergens.len();
            for ale in allergens.iter() {
                if !self.allergens.contains_key(ale) {
                    self.allergens.insert(ale.to_string(), num_allergen);
                    num_allergen += 1;
                }
            }
            self.rules.push(Rule {
                ingredients,
                allergens,
            });
        }
        Ok(())
    }
    fn part1(&mut self) -> usize {
        let verbose = !self.get_config().bench;
        let cnf = self.make_cnf();
        let mut count: usize = 0;
        for ing in self.ingredients.keys() {
            let mut asserted = cnf.clone();
            asserted.push(
                self.allergens
                    .keys()
                    .map(|al| self.var_of(ing, al))
                    .collect::<Vec<_>>(),
            );
            if let Ok(Certificate::UNSAT) = Certificate::try_from(asserted) {
                if verbose {
                    progress!(format!("{} is safe", ing));
                }
                count += self
                    .rules
                    .iter()
                    .map(|r| r.ingredients.iter().filter(|i| *i == ing).count())
                    .sum::<usize>();
            }
        }
        count
    }
    fn part2(&mut self) -> String {
        let cnf = self.make_cnf();
        let mut assign: HashSet<(&str, &str)> = HashSet::new();
        if let Certificate::SAT(ans) = Certificate::try_from(cnf).expect("panic!") {
            for lit in ans.iter() {
                if *lit < 0 {
                    continue;
                }
                for i in self.ingredients.keys() {
                    for a in self.allergens.keys() {
                        if self.var_of(i, a) == *lit {
                            // println!(" - {} has {}.", i, a);
                            assign.insert((a, i));
                        }
                    }
                }
            }
        } else {
            println!("UNSAT");
        }
        let mut vec: Vec<&(&str, &str)> = assign.iter().collect::<Vec<&(&str, &str)>>();
        vec.sort_unstable();

        let mut result = String::from(vec[0].1);
        for w in &vec[1..] {
            result.push(',');
            result.push_str(w.1);
        }
        result
    }
}

impl Puzzle {
    fn var_of(&self, ing: &str, all: &str) -> i32 {
        if let Some(ni) = self.ingredients.get(ing)
            && let Some(na) = self.allergens.get(all) {
                let num_alls = self.allergens.len();
                return (ni * num_alls + na + 1) as i32;
            }
        0
    }
    fn make_cnf(&self) -> Vec<Vec<i32>> {
        // clause builder
        let _imply = |v1: i32, v2: i32| vec![-v1, v2];
        let xor = |v1: i32, v2: i32| vec![-v1, -v2];
        // build cnf
        let mut cnf: Vec<Vec<i32>> = Vec::new();

        //
        //## ONLY-ONE-ALLERGEN
        //
        for i0 in self.ingredients.keys() {
            for ale in self.allergens.keys() {
                for i1 in self.ingredients.keys() {
                    if i0 != i1 {
                        cnf.push(xor(self.var_of(i0, ale), self.var_of(i1, ale)));
                    }
                }
            }
        }

        //
        //## EXCLUSIZE-ALLERGEN
        //
        for ing in self.ingredients.keys() {
            for a0 in self.allergens.keys() {
                for a1 in self.allergens.keys() {
                    if a0 != a1 {
                        cnf.push(xor(self.var_of(ing, a0), self.var_of(ing, a1)));
                    }
                }
            }
        }

        //
        //## AT-LEAST-1
        //
        for r in self.rules.iter() {
            for al in r.allergens.iter() {
                cnf.push(
                    r.ingredients
                        .iter()
                        .map(|ing| self.var_of(ing, al))
                        .collect::<Vec<i32>>(),
                );
            }
        }
        cnf
    }
}
