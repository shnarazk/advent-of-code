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
use {
    adventofcode::{framework::AdventOfCode, Description},
    std::env::args,
};

pub fn main() {
    if args().count() == 1 {
        println!("USAGE:");
        println!(" $0 YYYY DD\t\tYYYY年DD日目のパート{{1, 2}}をdata/2021/input-dayDD.txtを入力として実行");
        println!(" $0 YYYY DD P\tYYYY年DD日目のパートPをdata/2021/input-dayDD.txtを入力として実行");
        println!(" $0 YYYY DD P TTT\tYYYY年DD日目のパートPをdata/2021/input-dayDD-TTT.txtを入力として実行");
        println!(" $0 YYYY DD P -\tYYYY年DD日目のパートPを入力なしで実行");
        panic!();
    }
    let mut a = args();
    let year = a
        .nth(1)
        .unwrap_or_else(|| "2021".to_string())
        .parse::<usize>()
        .unwrap_or(1);
    let day = a
        .next()
        .unwrap_or_else(|| "1".to_string())
        .parse::<usize>()
        .unwrap_or(1);
    let part = a
        .next()
        .unwrap_or_else(|| "0".to_string())
        .parse::<usize>()
        .unwrap_or(0);
    let desc: Description = match a.next() {
        Some(ext) if ext == "-" => Description::TestData("".to_string()),
        Some(ext) => Description::FileTag(ext),
        None => Description::None,
    };
    match year {
        #[cfg(feature = "y2021")]
        2021 => {
            match day {
                1 => dbg!(y2021::day01::Puzzle::solve(desc, part)),
                2 => dbg!(y2021::day02::Puzzle::solve(desc, part)),
                3 => dbg!(y2021::day03::Puzzle::solve(desc, part)),
                4 => dbg!(y2021::day04::Puzzle::solve(desc, part)),
                5 => dbg!(y2021::day05::Puzzle::solve(desc, part)),
                6 => dbg!(y2021::day06::Puzzle::solve(desc, part)),
                7 => dbg!(y2021::day07::Puzzle::solve(desc, part)),
                8 => dbg!(y2021::day08::Puzzle::solve(desc, part)),
                9 => dbg!(y2021::day09::Puzzle::solve(desc, part)),
                10 => dbg!(y2021::day10::Puzzle::solve(desc, part)),
                11 => dbg!(y2021::day11::Puzzle::solve(desc, part)),
                12 => dbg!(y2021::day12::Puzzle::solve(desc, part)),
                13 => dbg!(y2021::day13::Puzzle::solve(desc, part)),
                14 => dbg!(y2021::day14::Puzzle::solve(desc, part)),
                15 => dbg!(y2021::day15::Puzzle::solve(desc, part)),
                16 => dbg!(y2021::day16::Puzzle::solve(desc, part)),
                17 => dbg!(y2021::day17::Puzzle::solve(desc, part)),
                18 => dbg!(y2021::day18::Puzzle::solve(desc, part)),
                19 => dbg!(y2021::day19::Puzzle::solve(desc, part)),
                // 20 => dbg!(y2021::day20::Puzzle::solve(desc, part)),
                // 21 => dbg!(y2021::day21::Puzzle::solve(desc, part)),
                // 22 => dbg!(y2021::day22::Puzzle::solve(desc, part)),
                // 23 => dbg!(y2021::day23::Puzzle::solve(desc, part)),
                // 24 => dbg!(y2021::day24::Puzzle::solve(desc, part)),
                // 25 => dbg!(y2021::day25::Puzzle::solve(desc, part)),
                _ => dbg!(y2021::template::Puzzle::solve(desc, part)),
            }
        }
        #[cfg(feature = "y2020")]
        2020 => match day {
            1 => dbg!(y2020::day01::Puzzle::solve(desc, part)),
            2 => dbg!(y2020::day02::Puzzle::solve(desc, part)),
            3 => dbg!(y2020::day03::Puzzle::solve(desc, part)),
            4 => dbg!(y2020::day04::Puzzle::solve(desc, part)),
            5 => dbg!(y2020::day05::Puzzle::solve(desc, part)),
            6 => dbg!(y2020::day06::Puzzle::solve(desc, part)),
            7 => dbg!(y2020::day07::Puzzle::solve(desc, part)),
            8 => dbg!(y2020::day08::Puzzle::solve(desc, part)),
            9 => dbg!(y2020::day09::Puzzle::solve(desc, part)),
            10 => dbg!(y2020::day10::Puzzle::solve(desc, part)),
            11 => dbg!(y2020::day11::Puzzle::solve(desc, part)),
            12 => dbg!(y2020::day12::Puzzle::solve(desc, part)),
            13 => dbg!(y2020::day13::Puzzle::solve(desc, part)),
            14 => dbg!(y2020::day14::Puzzle::solve(desc, part)),
            15 => dbg!(y2020::day15::Puzzle::solve(desc, part)),
            16 => dbg!(y2020::day16::Puzzle::solve(desc, part)),
            17 => dbg!(y2020::day17::Puzzle::solve(desc, part)),
            18 => dbg!(y2020::day18::Puzzle::solve(desc, part)),
            19 => dbg!(y2020::day19::Puzzle::solve(desc, part)),
            20 => dbg!(y2020::day20::Puzzle::solve(desc, part)),
            21 => dbg!(y2020::day21::Puzzle::solve(desc, part)),
            22 => dbg!(y2020::day22::Puzzle::solve(desc, part)),
            23 => dbg!(y2020::day23::Puzzle::solve(desc, part)),
            24 => dbg!(y2020::day24::Puzzle::solve(desc, part)),
            25 => dbg!(y2020::day25::Puzzle::solve(desc, part)),
            _ => dbg!(y2021::template::Puzzle::solve(desc, part)),
        },
        #[cfg(feature = "y2019")]
        2019 => match day {
            1 => dbg!(y2019::day01::Puzzle::solve(desc, part)),
            2 => dbg!(y2019::day02::Puzzle::solve(desc, part)),
            3 => dbg!(y2019::day03::Puzzle::solve(desc, part)),
            4 => dbg!(y2019::day04::Puzzle::solve(desc, part)),
            5 => dbg!(y2019::day05::Puzzle::solve(desc, part)),
            6 => dbg!(y2019::day06::Puzzle::solve(desc, part)),
            7 => dbg!(y2019::day07::Puzzle::solve(desc, part)),
            8 => dbg!(y2019::day08::Puzzle::solve(desc, part)),
            9 => dbg!(y2019::day09::Puzzle::solve(desc, part)),
            10 => dbg!(y2019::day10::Puzzle::solve(desc, part)),
            11 => dbg!(y2019::day11::Puzzle::solve(desc, part)),
            12 => dbg!(y2019::day12::Puzzle::solve(desc, part)),
            13 => dbg!(y2019::day13::Puzzle::solve(desc, part)),
            14 => dbg!(y2019::day14::Puzzle::solve(desc, part)),
            15 => dbg!(y2019::day15::Puzzle::solve(desc, part)),
            16 => dbg!(y2019::day16::Puzzle::solve(desc, part)),
            17 => dbg!(y2019::day17::Puzzle::solve(desc, part)),
            18 => dbg!(y2019::day18::Puzzle::solve(desc, part)),
            19 => dbg!(y2019::day19::Puzzle::solve(desc, part)),
            20 => dbg!(y2019::day20::Puzzle::solve(desc, part)),
            21 => dbg!(y2019::day21::Puzzle::solve(desc, part)),
            22 => dbg!(y2019::day22::Puzzle::solve(desc, part)),
            23 => dbg!(y2019::day23::Puzzle::solve(desc, part)),
            24 => dbg!(y2019::day24::Puzzle::solve(desc, part)),
            25 => dbg!(y2019::day25::Puzzle::solve(desc, part)),
            _ => dbg!(y2021::template::Puzzle::solve(desc, part)),
        },
        #[cfg(feature = "y2018")]
        2018 => match day {
            1 => dbg!(y2018::day01::Puzzle::solve(desc, part)),
            2 => dbg!(y2018::day02::Puzzle::solve(desc, part)),
            3 => dbg!(y2018::day03::Puzzle::solve(desc, part)),
            4 => dbg!(y2018::day04::Puzzle::solve(desc, part)),
            5 => dbg!(y2018::day05::Puzzle::solve(desc, part)),
            6 => dbg!(y2018::day06::Puzzle::solve(desc, part)),
            7 => dbg!(y2018::day07::Puzzle::solve(desc, part)),
            8 => dbg!(y2018::day08::Puzzle::solve(desc, part)),
            9 => dbg!(y2018::day09::Puzzle::solve(desc, part)),
            10 => dbg!(y2018::day10::Puzzle::solve(desc, part)),
            11 => dbg!(y2018::day11::Puzzle::solve(desc, part)),
            12 => dbg!(y2018::day12::Puzzle::solve(desc, part)),
            13 => dbg!(y2018::day13::Puzzle::solve(desc, part)),
            14 => dbg!(y2018::day14::Puzzle::solve(desc, part)),
            15 => dbg!(y2018::day15::Puzzle::solve(desc, part)),
            16 => dbg!(y2018::day16::Puzzle::solve(desc, part)),
            17 => dbg!(y2018::day17::Puzzle::solve(desc, part)),
            18 => dbg!(y2018::day18::Puzzle::solve(desc, part)),
            19 => dbg!(y2018::day19::Puzzle::solve(desc, part)),
            20 => dbg!(y2018::day20::Puzzle::solve(desc, part)),
            21 => dbg!(y2018::day21::Puzzle::solve(desc, part)),
            22 => dbg!(y2018::day22::Puzzle::solve(desc, part)),
            23 => dbg!(y2018::day23::Puzzle::solve(desc, part)),
            24 => dbg!(y2018::day24::Puzzle::solve(desc, part)),
            25 => dbg!(y2018::day25::Puzzle::solve(desc, part)),
            _ => dbg!(y2021::template::Puzzle::solve(desc, part)),
        },
        #[cfg(feature = "y2017")]
        2017 => match day {
            1 => dbg!(y2017::day01::Puzzle::solve(desc, part)),
            2 => dbg!(y2017::day02::Puzzle::solve(desc, part)),
            3 => dbg!(y2017::day03::Puzzle::solve(desc, part)),
            4 => dbg!(y2017::day04::Puzzle::solve(desc, part)),
            5 => dbg!(y2017::day05::Puzzle::solve(desc, part)),
            6 => dbg!(y2017::day06::Puzzle::solve(desc, part)),
            7 => dbg!(y2017::day07::Puzzle::solve(desc, part)),
            8 => dbg!(y2017::day08::Puzzle::solve(desc, part)),
            9 => dbg!(y2017::day09::Puzzle::solve(desc, part)),
            10 => dbg!(y2017::day10::Puzzle::solve(desc, part)),
            11 => dbg!(y2017::day11::Puzzle::solve(desc, part)),
            12 => dbg!(y2017::day12::Puzzle::solve(desc, part)),
            13 => dbg!(y2017::day13::Puzzle::solve(desc, part)),
            14 => dbg!(y2017::day14::Puzzle::solve(desc, part)),
            15 => dbg!(y2017::day15::Puzzle::solve(desc, part)),
            16 => dbg!(y2017::day16::Puzzle::solve(desc, part)),
            17 => dbg!(y2017::day17::Puzzle::solve(desc, part)),
            18 => dbg!(y2017::day18::Puzzle::solve(desc, part)),
            19 => dbg!(y2017::day19::Puzzle::solve(desc, part)),
            20 => dbg!(y2017::day20::Puzzle::solve(desc, part)),
            21 => dbg!(y2017::day21::Puzzle::solve(desc, part)),
            22 => dbg!(y2017::day22::Puzzle::solve(desc, part)),
            23 => dbg!(y2017::day23::Puzzle::solve(desc, part)),
            24 => dbg!(y2017::day24::Puzzle::solve(desc, part)),
            25 => dbg!(y2017::day25::Puzzle::solve(desc, part)),
            _ => dbg!(y2021::template::Puzzle::solve(desc, part)),
        },
        #[cfg(feature = "y2016")]
        2016 => match day {
            1 => dbg!(y2016::day01::Puzzle::solve(desc, part)),
            2 => dbg!(y2016::day02::Puzzle::solve(desc, part)),
            3 => dbg!(y2016::day03::Puzzle::solve(desc, part)),
            4 => dbg!(y2016::day04::Puzzle::solve(desc, part)),
            5 => dbg!(y2016::day05::Puzzle::solve(desc, part)),
            6 => dbg!(y2016::day06::Puzzle::solve(desc, part)),
            7 => dbg!(y2016::day07::Puzzle::solve(desc, part)),
            8 => dbg!(y2016::day08::Puzzle::solve(desc, part)),
            9 => dbg!(y2016::day09::Puzzle::solve(desc, part)),
            10 => dbg!(y2016::day10::Puzzle::solve(desc, part)),
            11 => dbg!(y2016::day11::Puzzle::solve(desc, part)),
            12 => dbg!(y2016::day12::Puzzle::solve(desc, part)),
            13 => dbg!(y2016::day13::Puzzle::solve(desc, part)),
            14 => dbg!(y2016::day14::Puzzle::solve(desc, part)),
            15 => dbg!(y2016::day15::Puzzle::solve(desc, part)),
            16 => dbg!(y2016::day16::Puzzle::solve(desc, part)),
            17 => dbg!(y2016::day17::Puzzle::solve(desc, part)),
            18 => dbg!(y2016::day18::Puzzle::solve(desc, part)),
            19 => dbg!(y2016::day19::Puzzle::solve(desc, part)),
            20 => dbg!(y2016::day20::Puzzle::solve(desc, part)),
            21 => dbg!(y2016::day21::Puzzle::solve(desc, part)),
            22 => dbg!(y2016::day22::Puzzle::solve(desc, part)),
            23 => dbg!(y2016::day23::Puzzle::solve(desc, part)),
            24 => dbg!(y2016::day24::Puzzle::solve(desc, part)),
            25 => dbg!(y2016::day25::Puzzle::solve(desc, part)),
            _ => dbg!(y2021::template::Puzzle::solve(desc, part)),
        },
        #[cfg(feature = "y2015")]
        2015 => {
            match day {
                1 => dbg!(y2015::day01::Puzzle::solve(desc, part)),
                // 2 => dbg!(y2015::day02::Puzzle::solve(desc, part)),
                // 3 => dbg!(y2015::day03::Puzzle::solve(desc, part)),
                // 4 => dbg!(y2015::day04::Puzzle::solve(desc, part)),
                // 5 => dbg!(y2015::day05::Puzzle::solve(desc, part)),
                // 6 => dbg!(y2015::day06::Puzzle::solve(desc, part)),
                // 7 => dbg!(y2015::day07::Puzzle::solve(desc, part)),
                // 8 => dbg!(y2015::day08::Puzzle::solve(desc, part)),
                // 9 => dbg!(y2015::day09::Puzzle::solve(desc, part)),
                // 10 => dbg!(y2015::day10::Puzzle::solve(desc, part)),
                // 11 => dbg!(y2015::day11::Puzzle::solve(desc, part)),
                // 12 => dbg!(y2015::day12::Puzzle::solve(desc, part)),
                // 13 => dbg!(y2015::day13::Puzzle::solve(desc, part)),
                // 14 => dbg!(y2015::day14::Puzzle::solve(desc, part)),
                // 15 => dbg!(y2015::day15::Puzzle::solve(desc, part)),
                // 16 => dbg!(y2015::day16::Puzzle::solve(desc, part)),
                // 17 => dbg!(y2015::day17::Puzzle::solve(desc, part)),
                // 18 => dbg!(y2015::day18::Puzzle::solve(desc, part)),
                // 19 => dbg!(y2015::day19::Puzzle::solve(desc, part)),
                // 20 => dbg!(y2015::day20::Puzzle::solve(desc, part)),
                // 21 => dbg!(y2015::day21::Puzzle::solve(desc, part)),
                // 22 => dbg!(y2015::day22::Puzzle::solve(desc, part)),
                // 23 => dbg!(y2015::day23::Puzzle::solve(desc, part)),
                // 24 => dbg!(y2015::day24::Puzzle::solve(desc, part)),
                // 25 => dbg!(y2015::day25::Puzzle::solve(desc, part)),
                _ => dbg!(y2021::template::Puzzle::solve(desc, part)),
            }
        }
        _ => dbg!(y2021::template::Puzzle::solve(desc, part)),
    };
}
