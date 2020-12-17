#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use {
    lazy_static::lazy_static,
    regex::Regex,
    std::{
        collections::HashMap,
        io::{stdin, Read},
    },
};

const RANGE: isize = 17;
type LOC = (isize, isize, isize);

#[derive(Debug, PartialEq)]
struct World {
    loc: HashMap<LOC, bool>,
    generation: usize,
}

impl Default for World {
    fn default() -> Self {
        World {
            loc: HashMap::new(),
            generation: 0,
        }
    }
}

impl World {
    fn get_entry(&mut self, l: LOC) -> &mut bool {
        self.loc.entry(l).or_insert(false)
    }
    fn from(vec: &[LOC]) -> World {
        let mut w = World::default();
        for l in vec {
            *w.get_entry(*l) = true;
        }
        w
    }
    fn neighbors(&mut self, l: LOC) -> (usize, usize) {
        let mut actives = 0;
        let mut inactives = 0;
        for z in -1..=1 {
            for i in -1..=1 {
                for j in -1..=1 {
                    if z == 0 && i == 0 && j == 0 {
                        continue;
                    }
                    if *self.get_entry((l.0 + z, l.1 + i, l.2 + j)) {
                        actives += 1;
                    } else {
                        inactives += 1;
                    }
                }
            }
        }
        (inactives, actives)
    }
    fn next(&mut self) -> World {
        let mut next = World::default();
        for z in -RANGE..=RANGE {
            for i in -RANGE..=RANGE {
                for j in -RANGE..=RANGE {
                    let l = (z, i, j);
                    let (ni, na) = self.neighbors(l);
                    let new_entry = next.get_entry(l);
                    if *self.get_entry(l) {
                        *new_entry = na == 2 || na == 3;
                    } else {
                        *new_entry = na == 3;
                    }
                }
            }
        }
        next.generation = self.generation + 1;
        next
    }
    fn print(&mut self) {
        const R: isize = 5;
        // for z in -R..=R {
        for z in -1..=1 {
            for i in -R..=R {
                for j in -R..=R {
                    if *self.get_entry((z, i, j)) {
                        print!("#");
                    // print!("{:?}, ", (z, i, j));
                    } else {
                        print!(".");
                    }
                }
                println!();
            }
            println!("");
        }
    }
    fn actives(&mut self) -> usize {
        let mut count = 0;
        for z in -RANGE..=RANGE {
            for i in -RANGE..=RANGE {
                for j in -RANGE..=RANGE {
                    if *self.get_entry((z, i, j)) {
                        count += 1;
                    }
                }
            }
        }
        count
    }
}

type LOC4 = (isize, isize, isize, isize);

#[derive(Debug, PartialEq)]
struct World4 {
    loc: HashMap<LOC4, bool>,
    generation: usize,
}

impl Default for World4 {
    fn default() -> Self {
        World4 {
            loc: HashMap::new(),
            generation: 0,
        }
    }
}

impl World4 {
    fn get_entry(&mut self, l: LOC4) -> &mut bool {
        self.loc.entry(l).or_insert(false)
    }
    fn from(vec: &[LOC4]) -> World4 {
        let mut w = World4::default();
        for l in vec {
            *w.get_entry(*l) = true;
        }
        w
    }
    fn neighbors(&mut self, l: LOC4) -> (usize, usize) {
        let mut actives = 0;
        let mut inactives = 0;
        for t in -1..=1 {
            for z in -1..=1 {
                for i in -1..=1 {
                    for j in -1..=1 {
                        if t == 0 && z == 0 && i == 0 && j == 0 {
                            continue;
                        }
                        if *self.get_entry((l.0 + t, l.1 + z, l.2 + i, l.3 + j)) {
                            actives += 1;
                        } else {
                            inactives += 1;
                        }
                    }
                }
            }
        }
        (inactives, actives)
    }
    fn next(&mut self) -> World4 {
        let mut next = World4::default();
        for t in -RANGE..=RANGE {
            for z in -RANGE..=RANGE {
                for i in -RANGE..=RANGE {
                    for j in -RANGE..=RANGE {
                        let l = (t, z, i, j);
                        let (ni, na) = self.neighbors(l);
                        let new_entry = next.get_entry(l);
                        if *self.get_entry(l) {
                            *new_entry = na == 2 || na == 3;
                        } else {
                            *new_entry = na == 3;
                        }
                    }
                }
            }
        }
        next.generation = self.generation + 1;
        next
    }
    fn print(&mut self) {
        const R: isize = 5;
        // for z in -R..=R {
        for t in -1..=1 {
            for z in -1..=1 {
                for i in -R..=R {
                    for j in -R..=R {
                        if *self.get_entry((t, z, i, j)) {
                            print!("#");
                        // print!("{:?}, ", (z, i, j));
                        } else {
                            print!(".");
                        }
                    }
                    println!();
                }
                println!("");
            }
        }
    }
    fn actives(&mut self) -> usize {
        let mut count = 0;
        for t in -RANGE..=RANGE {
            for z in -RANGE..=RANGE {
                for i in -RANGE..=RANGE {
                    for j in -RANGE..=RANGE {
                        if *self.get_entry((t, z, i, j)) {
                            count += 1;
                        }
                    }
                }
            }
        }
        count
    }
}

fn main() {
    let mut buf = String::new();
    stdin().read_to_string(&mut buf).expect("wrong");
    let mut w0 = read4(&buf);
    w0.print();
    let mut w6 = w0.next().next().next().next().next().next();
    dbg!(w6.actives());
}

fn read4(str: &str) -> World4 {
    let mut vec: Vec<LOC4> = Vec::new();
    let t = 0;
    let z = 0;
    let offset = (str.split('\n').count() as isize - 1) / 2;
    let mut i = -offset;
    let mut j = -offset;
    for l in str.split('\n') {
        for c in l.chars() {
            if c == '#' {
                vec.push((t, z, i, j));
            }
            j += 1;
        }
        j = -offset;
        i += 1;
    }
    World4::from(&vec)
}

fn read(str: &str) -> World {
    let mut vec: Vec<LOC> = Vec::new();
    let z = 0;
    let offset = (str.split('\n').count() as isize - 1) / 2;
    let mut i = -offset;
    let mut j = -offset;
    for l in str.split('\n') {
        for c in l.chars() {
            if c == '#' {
                vec.push((z, i, j));
            }
            j += 1;
        }
        j = -offset;
        i += 1;
    }
    World::from(&vec)
}

fn parse(str: &str) -> Option<bool> {
    // lazy_static! { static ref RE: Regex = Regex::new(r"^(\d+)$").expect("error"); }
    // if let Some(m) = RE.captures(key) {}
    Some(false)
}

fn eval() -> usize {
    0
}

mod test {
    use super::*;
    const TEST1: &str = "\
.#.
..#
###";
    #[test]
    fn test1() {
        dbg!(TEST1);
        let mut w0 = read(TEST1);
        dbg!(w0.neighbors((-1, -1, -1)));
        let mut w1 = w0.next();
        dbg!(w1.get_entry((-1, -1, -1)));
        let mut w6 = w0.next().next().next().next().next().next();
        assert_eq!(w6.generation, 6);
        assert_eq!(w6.actives(), 112);
    }
}
