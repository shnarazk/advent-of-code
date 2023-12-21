//! advent of code runner
#[cfg(feature = "y2015")]
use adventofcode::y2015;
#[cfg(feature = "y2016")]
use adventofcode::y2016;
#[cfg(feature = "y2017")]
use adventofcode::y2017;
#[cfg(feature = "y2018")]
use adventofcode::y2018;
#[cfg(feature = "y2019")]
use adventofcode::y2019;
#[cfg(feature = "y2020")]
use adventofcode::y2020;
#[cfg(feature = "y2021")]
use adventofcode::y2021;
#[cfg(feature = "y2022")]
use adventofcode::y2022;
#[cfg(feature = "y2023")]
use adventofcode::y2023;

use {
    adventofcode::{
        aoc_arms, color,
        framework::{AdventOfCode, ConfigAoC},
        Description,
    },
    clap::Parser,
    std::time::Instant,
};

pub fn main() {
    let config = ConfigAoC::parse();
    assert!(0 < config.day && config.day <= 25);
    let day = config.day;
    assert!(config.part <= 3);
    let mut part = config.part;
    if config.serialize {
        part = 0;
    }
    let desc = match config.clone().alt {
        Some(ext) if ext == "-" => Description::TestData("".to_string()),
        Some(ext) => Description::FileTag(ext.to_string()),
        None => Description::None,
    };
    let beg = Instant::now();
    match config.year {
        #[cfg(feature = "y2015")]
        2015 => aoc_arms!(2015),
        #[cfg(feature = "y2016")]
        2016 => aoc_arms!(2016),
        #[cfg(feature = "y2017")]
        2017 => aoc_arms!(2017),
        #[cfg(feature = "y2018")]
        2018 => aoc_arms!(2018),
        #[cfg(feature = "y2019")]
        2019 => aoc_arms!(2019),
        #[cfg(feature = "y2020")]
        2020 => aoc_arms!(2020),
        #[cfg(feature = "y2021")]
        2021 => aoc_arms!(2021),
        #[cfg(feature = "y2022")]
        2022 => aoc_arms!(2022),
        #[cfg(feature = "y2023")]
        2023 => aoc_arms!(2023),
        _ => println!("invalid year: {}", config.year),
    };
    let end = Instant::now();
    println!(
        "{}# Execution time: {:.1} msec.{}",
        color::RED,
        (end - beg).as_secs_f64() * 1000.0,
        color::RESET
    );
}
