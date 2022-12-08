//! <https://adventofcode.com/2022/day/7>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        regex,
    },
    std::collections::HashMap,
};

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Entry {
    Dir(String),
    File(String, usize),
}

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Command {
    Ls(Vec<Entry>),
    CdTo(String),
    CdUp,
    CdRoot,
}

#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Directory {
    name: String,
    parent: String,
    files_size: usize,
    subdirectories: Vec<String>,
    total_size: usize,
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct Puzzle {
    line: Vec<Command>,
    file_system: HashMap<String, Directory>,
}

#[aoc(2022, 7)]
impl AdventOfCode for Puzzle {
    const DELIMITER: &'static str = "$";
    fn insert(&mut self, block: &str) -> Result<(), ParseError> {
        let ls_parser = regex!(r"^ ls\n((.|\n)+)\n$");
        if let Some(segment) = ls_parser.captures(block) {
            let dir_parser = regex!(r"^dir (.+)");
            let file_parser = regex!(r"^(\d+) (.+)$");
            let v = segment[1]
                .split('\n')
                .map(|line| {
                    if let Some(seg) = dir_parser.captures(line) {
                        Entry::Dir(seg[1].to_string())
                    } else if let Some(seg) = file_parser.captures(line) {
                        let Ok(size) = seg[1].parse::<usize>() else {panic!();};
                        Entry::File(seg[2].to_string(), size)
                    } else {
                        dbg!(line);
                        unreachable!()
                    }
                })
                .collect::<Vec<_>>();
            self.line.push(Command::Ls(v));
            return Ok(());
        }
        let up_parser = regex!(r"^ cd \.\.\n$");
        if up_parser.captures(block).is_some() {
            self.line.push(Command::CdUp);
            return Ok(());
        }
        let root_parser = regex!(r"^ cd /\n$");
        if root_parser.captures(block).is_some() {
            self.line.push(Command::CdRoot);
            return Ok(());
        }
        let cd_parser = regex!(r"^ cd ((.|\n)+)\n$");
        if let Some(segment) = cd_parser.captures(block) {
            self.line.push(Command::CdTo(segment[1].to_string()));
        }
        Ok(())
    }
    fn after_insert(&mut self) {
        let mut pwd = "/".to_string();
        for line in self.line.iter() {
            match line {
                Command::Ls(v) => {
                    self.file_system.entry(pwd.to_string()).and_modify(|dir| {
                        for ent in v.iter() {
                            match ent {
                                Entry::File(_, size) => {
                                    dir.files_size += size;
                                }
                                Entry::Dir(sub) => {
                                    let d = if dir.name == "/" {
                                        "/".to_string() + sub
                                    } else {
                                        dir.name.clone() + "/" + sub
                                    };
                                    dir.subdirectories.push(d);
                                }
                            }
                        }
                    });
                }
                Command::CdRoot => {
                    self.file_system
                        .entry("/".to_string())
                        .or_insert(Directory {
                            name: "/".to_string(),
                            parent: "".to_string(),
                            ..Default::default()
                        });
                    pwd = "/".to_string();
                }
                Command::CdUp => {
                    let Some(dir) = self.file_system.get(&pwd) else {panic!("{}", pwd);};
                    pwd = dir.parent.to_string();
                }
                Command::CdTo(sub) => {
                    let dir = pwd.to_string();
                    pwd = if dir == "/" {
                        "/".to_string() + sub
                    } else {
                        dir.clone() + "/" + sub
                    };
                    self.file_system.entry(pwd.clone()).or_insert(Directory {
                        name: pwd.clone(),
                        parent: dir.clone(),
                        ..Default::default()
                    });
                }
            }
        }
        self.inject_total_size("/");
        #[cfg(feature = "for-bqn")]
        {
            for dir in self.file_system.values() {
                println!("{},{}", dir.name, dir.files_size);
            }
        }
    }
    fn part1(&mut self) -> Self::Output1 {
        self.file_system
            .values()
            .filter(|d| d.total_size < 100_000)
            .map(|d| d.total_size)
            .sum::<usize>()
    }
    fn part2(&mut self) -> Self::Output2 {
        let unused = 70_000_000 - self.file_system.get(&"/".to_string()).unwrap().total_size;
        let required = 30_000_000;
        let values = self.file_system.values().collect::<Vec<_>>();
        values
            .iter()
            .map(|d| d.total_size)
            .filter(|n| required <= unused + *n)
            .min()
            .unwrap()
    }
}

impl Puzzle {
    fn inject_total_size(&mut self, name: &str) -> usize {
        let dir = self.file_system.get(name).unwrap();
        let mut size = dir.files_size;
        let target = dir.subdirectories.clone();
        for subdir in target.iter() {
            size += self.inject_total_size(subdir);
        }
        self.file_system.entry(name.to_string()).and_modify(|dir| {
            dir.total_size = size;
        });
        size
    }
}
