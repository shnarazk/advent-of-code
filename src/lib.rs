use std::{fmt::Debug, fs::File, io::prelude::*};
pub mod template;
pub mod y2020;
pub mod y2021;

pub use {y2020::*, y2021::*};

#[derive(Clone, Debug, PartialEq)]
pub enum Description {
    FileTag(String),
    TestData(String),
    None,
}

#[derive(Debug, PartialEq)]
pub enum Answer<Output1: Sized + Debug + PartialEq, Output2: Sized + Debug + PartialEq> {
    Answers(Output1, Output2),
    Part1(Output1),
    Part2(Output2),
    None,
}

pub trait ProblemSolver<
    TargetObject: ProblemObject + Debug,
    Output1: Sized + Debug + PartialEq,
    Output2: Sized + Debug + PartialEq,
>: Debug + Sized
{
    const YEAR: usize;
    const DAY: usize;
    const DELIMITER: &'static str;
    fn default() -> Self;
    fn insert(&mut self, _object: TargetObject) {
        todo!("insert is not implemented")
    }
    fn input_filename(desc: Description) -> Option<String> {
        match desc {
            Description::FileTag(tag) => Some(format!(
                "{}/input-day{:>02}-{}.txt",
                Self::YEAR,
                Self::DAY,
                tag
            )),
            Description::None => Some(format!("{}/input-day{:>02}.txt", Self::YEAR, Self::DAY)),
            _ => None,
        }
    }
    fn load(desc: Description) -> Option<String> {
        match desc {
            Description::FileTag(_) => Self::load_file(desc),
            Description::TestData(_) => Self::load_data(desc),
            Description::None => Self::load_file(desc),
        }
    }
    fn load_file(desc: Description) -> Option<String> {
        if let Some(fname) = Self::input_filename(desc) {
            let file_name = format!("data/{}", fname);
            match File::open(&file_name) {
                Ok(mut file) => {
                    let mut contents = String::new();
                    if let Err(e) = file.read_to_string(&mut contents) {
                        panic!("Can't read {}: {:?}", fname, e);
                    }
                    println!("# loaded {}", &file_name);
                    return Some(contents);
                }
                Err(e) => panic!("Can't read {}: {:?}", fname, e),
            }
        }
        None
    }
    fn load_data(desc: Description) -> Option<String> {
        match desc {
            Description::TestData(s) if s.is_empty() => None,
            Description::TestData(s) => Some(s),
            _ => None,
        }
    }
    fn parse(desc: Description) -> Self {
        let mut instance = Self::default();
        if let Some(buffer) = Self::load(desc) {
            for block in buffer.split(Self::DELIMITER) {
                if let Some(element) = TargetObject::parse(block) {
                    instance.insert(element);
                }
            }
        }
        instance
    }
    fn run(&mut self, part: usize) -> Answer<Output1, Output2> {
        match part {
            0 => {
                println!("# Advent of Code {}: day {}, part 1", Self::YEAR, Self::DAY);
                let ans1 = self.part1();
                println!("# Advent of Code {}: day {}, part 2", Self::YEAR, Self::DAY);
                let ans2 = self.part2();
                Answer::Answers(ans1, ans2)
            }
            1 => {
                println!("# Advent of Code {}: day {}, part 1", Self::YEAR, Self::DAY);
                Answer::Part1(self.part1())
            }
            2 => {
                println!("# Advent of Code {}: day {}, part 2", Self::YEAR, Self::DAY);
                Answer::Part2(self.part2())
            }
            _ => Answer::None,
        }
    }
    fn part1(&mut self) -> Output1 {
        todo!("part1 is not yet implemented.")
    }
    fn part2(&mut self) -> Output2 {
        todo!("part2 is not yet implemented.")
    }
    fn go(part: usize, desc: Description) {
        dbg!(Self::parse(desc).run(part));
    }
}

pub trait ProblemObject: Debug + Sized {
    fn parse(s: &str) -> Option<Self>;
}

impl ProblemObject for () {
    fn parse(_: &str) -> Option<Self> {
        None
    }
}

impl ProblemObject for String {
    fn parse(line: &str) -> Option<Self> {
        if line.is_empty() {
            None
        } else {
            Some(line.to_string())
        }
    }
}
