//! <https://adventofcode.com/2022/day/7>
use {
    crate::{
        framework::{aoc, AdventOfCode, ParseError},
        parser::parse_usize,
    },
    std::collections::HashMap,
    winnow::{
        ascii::{newline, space1},
        combinator::{alt, repeat, separated, seq},
        token::one_of,
        PResult, Parser,
    },
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

fn parse_entry_name(s: &mut &str) -> PResult<String> {
    repeat(1.., one_of(('a'..='z', 'A'..='Z', '0'..='9', '.'))).parse_next(s)
}

fn parse_ls_dir(s: &mut &str) -> PResult<Entry> {
    ("dir ", parse_entry_name)
        .map(|(_, path): (&str, String)| Entry::Dir(path))
        .parse_next(s)
}

fn parse_ls_file(s: &mut &str) -> PResult<Entry> {
    (parse_usize, space1, parse_entry_name)
        .map(|(n, _, path): (usize, &str, String)| Entry::File(path, n))
        .parse_next(s)
}

fn parse_ls_output(s: &mut &str) -> PResult<Vec<Entry>> {
    separated(0.., alt((parse_ls_dir, parse_ls_file)), newline).parse_next(s)
}

fn parse_ls(s: &mut &str) -> PResult<Command> {
    ("$ ls\n", parse_ls_output)
        .map(|(_, b)| Command::Ls(b))
        .parse_next(s)
}

fn parse_cd_to(s: &mut &str) -> PResult<Command> {
    seq!("$ cd ", parse_entry_name)
        .map(|(_, path)| Command::CdTo(path))
        .parse_next(s)
}

fn parse_cd_up(s: &mut &str) -> PResult<Command> {
    "$ cd ..".map(|_| Command::CdUp).parse_next(s)
}

fn parse_cd_root(s: &mut &str) -> PResult<Command> {
    "$ cd /".map(|_| Command::CdRoot).parse_next(s)
}

fn parse_line(s: &mut &str) -> PResult<Command> {
    alt((parse_ls, parse_cd_up, parse_cd_to, parse_cd_root)).parse_next(s)
}

fn parse(s: &mut &str) -> PResult<Vec<Command>> {
    separated(1.., parse_line, newline).parse_next(s)
}

#[aoc(2022, 7)]
impl AdventOfCode for Puzzle {
    fn parse(&mut self, input: String) -> Result<String, ParseError> {
        self.line = parse(&mut input.as_str())?;
        Self::parsed()
    }
    fn end_of_data(&mut self) {
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
                    let Some(dir) = self.file_system.get(&pwd) else {
                        panic!("{}", pwd);
                    };
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
    }
    fn dump(&self) {
        for dir in self.file_system.values() {
            println!("{},{}", dir.name, dir.files_size);
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
        let unused = 70_000_000 - self.file_system.get("/").unwrap().total_size;
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
