use std::{fmt::Debug, fs::File, io::prelude::*};
pub mod day01;
pub mod day02;
pub mod day03;
pub mod day04;
pub mod day05;
pub mod day06;
pub mod day07;
pub mod day08;
pub mod day09;
pub mod day10;
pub mod day11;
pub mod day12;
pub mod day13;
pub mod day14;
pub mod day15;
pub mod day16;
pub mod day17;
pub mod day18;
pub mod day19;
pub mod day20;
pub mod day21;
pub mod day22;
pub mod day23;
pub mod day24;
pub mod day25;
pub mod template;

pub use {
    day01::day01, day02::day02, day03::day03, day04::day04, day05::day05, day06::day06,
    day07::day07, day08::day08, day09::day09, day10::day10, day11::day11, day12::day12,
    day13::day13, day14::day14, day15::day15, day16::day16, day17::day17, day18::day18,
    day19::day19, day20::day20, day21::day21, day22::day22, day23::day23, day24::day24,
    day25::day25, template::template,
};

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
    const DAY: usize;
    const DELIMITER: &'static str;
    fn default() -> Self;
    fn insert(&mut self, _object: TargetObject) {
        todo!("insert is not implemented")
    }
    fn input_filename(desc: Description) -> Option<String> {
        match desc {
            Description::FileTag(tag) => Some(format!("input-day{:>02}-{}.txt", Self::DAY, tag)),
            Description::None => Some(format!("input-day{:>02}.txt", Self::DAY)),
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
        if let Description::TestData(s) = desc {
            Some(s)
        } else {
            None
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
                println!("# Advent of Code 2020: day {}, part 1", Self::DAY);
                let ans1 = self.part1();
                println!("# Advent of Code 2020: day {}, part 2", Self::DAY);
                let ans2 = self.part2();
                Answer::Answers(ans1, ans2)
            }
            1 => {
                println!("# Advent of Code 2020: day {}, part 1", Self::DAY);
                Answer::Part1(self.part1())
            }
            2 => {
                println!("# Advent of Code 2020: day {}, part 2", Self::DAY);
                Answer::Part2(self.part2())
            }
            _ => Answer::None,
        }
    }
    fn part1(&mut self) -> Output1 {
        todo!()
    }
    fn part2(&mut self) -> Output2 {
        todo!()
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
