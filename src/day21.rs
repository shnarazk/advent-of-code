#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        collections::{HashMap, HashSet},
        io::{stdin, Read},
    },
};
use splr::*;
use std::{convert::TryFrom, env::args};

/// ## 変数
/// ingredient x allergen
/// 
/// ## ルール
/// 1. [ONLY-ONE-AllERGEN] ある ingredient がある allergen を持つなら他の indredient はその allergen を持てない
/// 1. [EXCULSIZE-ALLERGEN] ある ingredient がある allergen を持つなら他の allergen を持てない
/// 1. [AT-LEAST-1] ルールに則して、どれかはそのallergen を持たなければならない
/// 1. [XOR] ある ingredient がある allergen を持つなら他の ingredient はその allergen を持てない
/// 1. allergenに対して候補がある
/// 
/// * {mxmxvkd.dairy, kfcds.dairy, sqjhc.dairy, nhms.dairy}
/// * {mxmxvkd.dairy, kfcds.fish, sqjhc.fish, nhms.fish}
/// * {trh.dairy, fvjkl.dairy, sbzzf.dairy, mxmxvkd.dairy}
/// * ...
/// 
/// ## 目的
/// どの属性でもtrueにしたらUNSATになるようなindredientを探せ
pub fn day21() {
    let mut buf = String::new();
    stdin().read_to_string(&mut buf).expect("wrong");
    read(&buf);
}

fn read(str: &str) -> usize {
    let mut rules: Vec<(Vec<String>, Vec<String>)> = Vec::new();
    for l in str.split('\n') {
        if let Some(rule) = parse(l) {
            rules.push(rule);
        }
    }
    eval(&rules);
    0
}

fn parse(str: &str) -> Option<(Vec<String>, Vec<String>)> {
    lazy_static! {
        static ref RE: Regex = Regex::new(r"(^[^(]+)\(contains ((\w+, )*(\w+))\)$").expect("error");
    }

    if let Some(m) = RE.captures(str) {
        let ingredients = m[1].trim().split(' ').map(|s| s.to_string()).collect::<Vec<String>>();
        let allergens = m[2].trim().split(", ").map(|s| s.to_string()).collect::<Vec<String>>();
        // dbg!((&ingredients, &allergens));
        return Some((ingredients, allergens));
    }
    None
}

fn eval(rules: &[(Vec<String>, Vec<String>)]) {
    let mut ingredients: HashSet<String> = HashSet::new();
    let mut allergens: HashSet<String> = HashSet::new();
    for (is, al) in rules.iter() {
        for i in is {
            ingredients.insert(i.to_string());
        }
        for a in al {
            allergens.insert(a.to_string());
        }
    }
    let mut n_ingredients: HashMap<String, usize> = HashMap::new();
    let mut n_allergens: HashMap<String, usize> = HashMap::new();
    for (n, i) in ingredients.iter().enumerate() {
        *n_ingredients.entry(i.to_string()).or_insert(0) = n;
    }
    for (n, a) in allergens.iter().enumerate() {
        *n_allergens.entry(a.to_string()).or_insert(0) = n;
    }
    let num_ings = n_ingredients.len();
    let num_alls = n_allergens.len();
    // dbg!(&n_ingredients);
    // dbg!(&n_allergens);
    let var_of = |ing: &str, all: &str| {
        if let Some(ni) = n_ingredients.get(ing) {
            if let Some(na) = n_allergens.get(all) {
                return (ni * num_alls + na + 1) as i32;
            }
        }
        0
    };
    // clause builder
    let imply = |v1: i32, v2: i32| { vec![-v1, v2] };
    let xor = |v1: i32, v2: i32| { vec![-v1, -v2] };
    // build cnf
    let mut cnf: Vec<Vec<i32>> = Vec::new();

    //
    //## ONLY-ONE-ALLERGEN
    //
    for i0 in ingredients.iter() {
        for ale in allergens.iter() {
            for i1 in ingredients.iter() {
                if i0 != i1 {
                    cnf.push(xor(var_of(i0, ale), var_of(i1, ale)));
                }
            }
        }
    }

    //
    //## EXCLUSIZE-ALLERGEN
    //
    for ing in ingredients.iter() {
        for a0 in allergens.iter() {
            for a1 in allergens.iter() {
                if a0 != a1 {
                    cnf.push(xor(var_of(ing, a0), var_of(ing, a1)));
                }
            }
        }
    }

    //
    //## AT-LEAST-1
    //
    for (ings, alles) in rules.iter() {
        for al in alles.iter() {
            cnf.push(ings.iter().map(|ing| var_of(ing, al)).collect::<Vec<i32>>());
        }
    }

    // run Splr
    
    // part 1.
/*
    let mut count: usize = 0;
    for ing in ingredients.iter() {
        let mut satisfiable = false;
        for al in allergens.iter() {
            let mut asserted = cnf.clone();
            asserted.push(vec![var_of(ing, al)]);
            if let Certificate::SAT(ans) = Certificate::try_from(asserted).expect("panic!") {
                satisfiable = true;
                break;
                /*
                // println!("Assigning {} to {} has an answer {:?}", al, ing, ans);
                'next: for lit in ans.iter() {
                    if *lit < 0 {
                        continue;
                    }
                    for i in ingredients.iter() {
                        for a in allergens.iter() {
                            if var_of(i, a) == *lit {
                                println!(" - Under assigning {} to {}, {} has {}.", ing, al, i, a);
                                continue 'next;
                            }
                        }
                    }
                }
                 */
            } else {
                // println!("Assigning {} to {} emits a conflict", al, ing);
            }
        }
        if !satisfiable {
            println!("{} is safe", ing);
            count += rules.iter().map(|(v, _)| v.iter().filter(|i| *i == ing).count()).sum::<usize>();
        }
    }
    // dbg!(count);
*/
    // part 2.
    let mut assign: HashSet<(&str, &str)> = HashSet::new();
    if let Certificate::SAT(ans) = Certificate::try_from(cnf).expect("panic!") {
        for lit in ans.iter() {
            if *lit < 0 {
                continue;
            }
            for i in ingredients.iter() {
                for a in allergens.iter() {
                    if var_of(i, a) == *lit {
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
    // dbg!(vec.iter().map(|t| t.1).collect::<Vec<_>>());

    for (i, w) in vec.iter().map(|t| t.1).enumerate() {
        print!("{}", w);
        if i < vec.len() - 1 {
            print!(",");
        }
    }
    println!();
}

mod test {
    use super::*;
    const TEST1: &str = "\
mxmxvkd kfcds sqjhc nhms (contains dairy, fish)
trh fvjkl sbzzf mxmxvkd (contains dairy)
sqjhc fvjkl (contains soy)
sqjhc mxmxvkd sbzzf (contains fish)";
    #[test]
    fn test1() {
        assert_eq!(read(TEST1), 1);
    }
}
