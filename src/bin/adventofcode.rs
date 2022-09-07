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

use {
    adventofcode::{aoc_arms, framework::AdventOfCode, Description},
    std::env::args,
};

pub fn main() {
    let arg = args().skip(1).collect::<Vec<String>>();
    if arg.is_empty() {
        println!("USAGE:");
        println!(" $0 YYYY DD\t\tYYYY年DD日目のパート{{1, 2}}をdata/YYYY/input-dayDD.txtを入力として実行");
        println!(
            " $0 YYYY DD P\t\tYYYY年DD日目のパートPをdata/YYYY/input-dayDD.txtを入力として実行"
        );
        println!(" $0 YYYY DD P TTT\tYYYY年DD日目のパートPをdata/YYYY/input-dayDD-TTT.txtを入力として実行");
        panic!();
    }
    let parse = |s: Option<&String>, d, e| s.map_or_else(|| d, |s| s.parse().expect(e));
    let year = parse(arg.get(0), 2021, "wrong year");
    let day = parse(arg.get(1), 1, "wrong day");
    let part = parse(arg.get(2), 0, "wrong part");
    let desc: Description = match arg.get(3) {
        Some(ext) if ext == "-" => Description::TestData("".to_string()),
        Some(ext) => Description::FileTag(ext.to_string()),
        None => Description::None,
    };
    match year {
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
        2022 => aoc_arms!(2022, 1),
        _ => println!("invalid year: {year}"),
    };
}
