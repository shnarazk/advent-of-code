use {
    adventofcode::{framework::AdventOfCode, y2021::*, Description},
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
        1 => println!("{:?}", day01::Puzzle::solve(desc, part)),
        2 => println!("{:?}", day02::Puzzle::solve(desc, part)),
        3 => println!("{:?}", day03::Puzzle::solve(desc, part)),
        4 => println!("{:?}", day04::Puzzle::solve(desc, part)),
        5 => println!("{:?}", day05::Puzzle::solve(desc, part)),
        6 => println!("{:?}", day06::Puzzle::solve(desc, part)),
        7 => println!("{:?}", day07::Puzzle::solve(desc, part)),
        8 => println!("{:?}", day08::Puzzle::solve(desc, part)),
        9 => println!("{:?}", day09::Puzzle::solve(desc, part)),
        10 => println!("{:?}", day10::Puzzle::solve(desc, part)),
        11 => println!("{:?}", day11::Puzzle::solve(desc, part)),
        12 => println!("{:?}", day12::Puzzle::solve(desc, part)),
        13 => println!("{:?}", day13::Puzzle::solve(desc, part)),
        14 => println!("{:?}", day14::Puzzle::solve(desc, part)),
        15 => println!("{:?}", day15::Puzzle::solve(desc, part)),
        16 => println!("{:?}", day16::Puzzle::solve(desc, part)),
        17 => println!("{:?}", day17::Puzzle::solve(desc, part)),
        18 => println!("{:?}", day18::Puzzle::solve(desc, part)),
        19 => println!("{:?}", day19::Puzzle::solve(desc, part)),
        20 => println!("{:?}", day20::Puzzle::solve(desc, part)),
        21 => println!("{:?}", day21::Puzzle::solve(desc, part)),
        22 => println!("{:?}", day22::Puzzle::solve(desc, part)),
        23 => println!("{:?}", day23::Puzzle::solve(desc, part)),
        24 => println!("{:?}", day24::Puzzle::solve(desc, part)),
        25 => println!("{:?}", day25::Puzzle::solve(desc, part)),
        _ => println!("{:?}", template::Puzzle::solve(desc, part)),
    };
}
