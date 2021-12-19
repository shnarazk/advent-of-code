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
    adventofcode::{aoc_arms, framework::AdventOfCode, Description},
    std::env::args,
};

pub fn main() {
    if args().count() == 1 {
        println!("USAGE:");
        println!(" $0 YYYY DD\t\tYYYY年DD日目のパート{{1, 2}}をdata/2021/input-dayDD.txtを入力として実行");
        println!(
            " $0 YYYY DD P\t\tYYYY年DD日目のパートPをdata/2021/input-dayDD.txtを入力として実行"
        );
        println!(" $0 YYYY DD P TTT\tYYYY年DD日目のパートPをdata/2021/input-dayDD-TTT.txtを入力として実行");
        println!(" $0 YYYY DD P -\t\tYYYY年DD日目のパートPを入力なしで実行");
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
        2021 => aoc_arms!(2021),
        #[cfg(feature = "y2020")]
        2020 => match day {
            1 => println!("{:?}", y2020::day01(part, desc)),
            2 => println!("{:?}", y2020::day02(part, desc)),
            3 => println!("{:?}", y2020::day03(part, desc)),
            4 => println!("{:?}", y2020::day04(part, desc)),
            5 => println!("{:?}", y2020::day05(part, desc)),
            6 => println!("{:?}", y2020::day06(part, desc)),
            7 => println!("{:?}", y2020::day07(part, desc)),
            8 => println!("{:?}", y2020::day08(part, desc)),
            9 => println!("{:?}", y2020::day09(part, desc)),
            10 => println!("{:?}", y2020::day10(part, desc)),
            11 => println!("{:?}", y2020::day11(part, desc)),
            12 => println!("{:?}", y2020::day12(part, desc)),
            13 => println!("{:?}", y2020::day13(part, desc)),
            14 => println!("{:?}", y2020::day14(part, desc)),
            15 => println!("{:?}", y2020::day15(part, desc)),
            16 => println!("{:?}", y2020::day16(part, desc)),
            17 => println!("{:?}", y2020::day17(part, desc)),
            18 => println!("{:?}", y2020::day18(part, desc)),
            19 => println!("{:?}", y2020::day19(part, desc)),
            20 => println!("{:?}", y2020::day20(part, desc)),
            21 => println!("{:?}", y2020::day21(part, desc)),
            22 => println!("{:?}", y2020::day22(part, desc)),
            23 => println!("{:?}", y2020::day23(part, desc)),
            24 => println!("{:?}", y2020::day24(part, desc)),
            25 => println!("{:?}", y2020::day25(part, desc)),
            _ => panic!(),
        },
        #[cfg(feature = "y2019")]
        2019 => aoc_arms!(2019),
        #[cfg(feature = "y2018")]
        2018 => aoc_arms!(2018),
        #[cfg(feature = "y2017")]
        2017 => aoc_arms!(2017),
        #[cfg(feature = "y2016")]
        2016 => aoc_arms!(2015),
        #[cfg(feature = "y2015")]
        2015 => aoc_arms!(2015),
        _ => println!("{:?}", y2021::template::Puzzle::solve(desc, part)),
    };
}
