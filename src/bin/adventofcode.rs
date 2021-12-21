//! advent of code runner
#[cfg(feature = "y2015")]
use adventofcode::y2015;
#[cfg(feature = "y2020")]
use adventofcode::y2020;
#[cfg(feature = "y2021")]
use adventofcode::y2021;

use {
    adventofcode::{aoc_arms, framework::AdventOfCode, Description},
    std::env::args,
};

pub fn main() {
    let arg = args().collect::<Vec<String>>();
    if arg.is_empty() {
        println!("USAGE:");
        println!(" $0 YYYY DD\t\tYYYY年DD日目のパート{{1, 2}}をdata/YYYY/input-dayDD.txtを入力として実行");
        println!(
            " $0 YYYY DD P\t\tYYYY年DD日目のパートPをdata/YYYY/input-dayDD.txtを入力として実行"
        );
        println!(" $0 YYYY DD P TTT\tYYYY年DD日目のパートPをdata/YYYY/input-dayDD-TTT.txtを入力として実行");
        println!(" $0 YYYY DD P -\t\tYYYY年DD日目のパートPを入力なしで実行");
        panic!();
    }
    let parse = |s: Option<&String>, d, e| s.map_or_else(|| d, |s| s.parse().expect(e));
    let year = parse(arg.get(1), 2021, "wrong year");
    let day = parse(arg.get(2), 1, "wrong day");
    let part = parse(arg.get(3), 0, "wrong part");
    let desc: Description = match arg.get(4) {
        Some(ext) if ext == "-" => Description::TestData("".to_string()),
        Some(ext) => Description::FileTag(ext.to_string()),
        None => Description::None,
    };
    match year {
        #[cfg(feature = "y2021")]
        2021 => aoc_arms!(2021),
        #[cfg(feature = "y2020")]
        2020 => aoc_arms!(2020, 1, 19),
        #[cfg(feature = "y2015")]
        2015 => aoc_arms!(2015),
        _ => println!("{:?}", y2021::template::Puzzle::solve(desc, part)),
    };
}
