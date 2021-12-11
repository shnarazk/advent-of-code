use {
    adventofcode::{framework::AdventOfCode, template, y2021::*, Description},
    std::env::args,
};

pub fn main() {
    if args().count() == 1 {
        println!("USAGE:");
        println!(" $0 DD\t\tDD日目のパート{{1, 2}}をdata/2021/input-dayDD.txtを入力として実行");
        println!(" $0 DD P\tDD日目のパートPをdata/2021/input-dayDD.txtを入力として実行");
        println!(" $0 DD P TTT\tDD日目のパートPをdata/2021/input-dayDD-TTT.txtを入力として実行");
        println!(" $0 DD P -\tDD日目のパートPを入力なしで実行");
        panic!();
    }
    let mut a = args();
    let day = a
        .nth(1)
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
    match day {
        1 => day01::Puzzle::solve(desc, part),
        2 => day02::Puzzle::solve(desc, part),
        3 => day03::Puzzle::solve(desc, part),
        4 => day04::Puzzle::solve(desc, part),
        5 => day05::Puzzle::solve(desc, part),
        6 => day06::Puzzle::solve(desc, part),
        7 => day07::Puzzle::solve(desc, part),
        8 => day08::Puzzle::solve(desc, part),
        9 => day09::Puzzle::solve(desc, part),
        10 => day10::Puzzle::solve(desc, part),
        11 => day11::Puzzle::solve(desc, part),
        12 => day12::Puzzle::solve(desc, part),
        13 => day13::Puzzle::solve(desc, part),
        14 => day14::Puzzle::solve(desc, part),
        15 => day15::Puzzle::solve(desc, part),
        16 => day16::Puzzle::solve(desc, part),
        17 => day17::Puzzle::solve(desc, part),
        18 => day18::Puzzle::solve(desc, part),
        19 => day19::Puzzle::solve(desc, part),
        // 20 => day20::Puzzle::solve(desc, part),
        // 21 => day21::Puzzle::solve(desc, part),
        // 22 => day22::Puzzle::solve(desc, part),
        // 23 => day23::Puzzle::solve(desc, part),
        // 24 => day24::Puzzle::solve(desc, part),
        // 25 => day25::Puzzle::solve(desc, part),
        _ => template::Puzzle::solve(desc, part),
    };
}
