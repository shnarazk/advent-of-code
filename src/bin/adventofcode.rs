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
        progress,
    },
    clap::Parser,
    std::{fs::File, io::prelude::*, time::Instant},
};

pub fn main() {
    let config = ConfigAoC::parse();
    if config.bench {
        bench(config);
    } else {
        run_solver(config);
    }
}

fn run_solver(mut config: ConfigAoC) {
    assert!(config.day.is_some() && 0 < config.day.unwrap() && config.day.unwrap() <= 25);
    assert!(config.part <= 3);
    if config.part == 0 {
        config.serialize = true;
    }
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

fn bench(config: ConfigAoC) {
    let results = (1..26)
        .map(|day| {
            let mut config = config.clone();
            config.day = Some(day);
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
            }
            let end = Instant::now();
            progress!(format!(
                "{}day{:2}: {:?}{}",
                color::MAGENTA,
                day,
                (end - beg).as_secs_f64() * 1000.0,
                color::RESET,
            ));
            (day, (end - beg).as_secs_f64() * 1000.0)
        })
        .collect::<Vec<_>>();
    let output = format!("tmp/{}/execution_time.json", config.year);
    if let Ok(json) = serde_json::to_string(&results) {
        let mut file = File::create(&output).expect("fail to open");
        writeln!(file, "{}", json).expect("fail to save");
        println!(
            "{}# write JSON data on {}{}",
            color::MAGENTA,
            output,
            color::RESET,
        );
    };
    println!("|   day |    time |");
    println!("|------:|--------:|");
    for (day, time) in results.iter() {
        println!("| day{:<2} | {:>7.1} |", day, time);
    }
    println!(
        "| y{} | {:>7.1} |",
        config.year,
        results.iter().map(|p| p.1).sum::<f64>()
    );
}
