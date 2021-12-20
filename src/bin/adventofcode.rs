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
        println!(" $0 YYYY DD\t\tYYYY年DD日目のパート{{1, 2}}をdata/YYYY/input-dayDD.txtを入力として実行");
        println!(
            " $0 YYYY DD P\t\tYYYY年DD日目のパートPをdata/YYYY/input-dayDD.txtを入力として実行"
        );
        println!(" $0 YYYY DD P TTT\tYYYY年DD日目のパートPをdata/YYYY/input-dayDD-TTT.txtを入力として実行");
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
        2020 => aoc_arms!(2020, 1, 7),
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
