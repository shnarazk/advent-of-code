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
        1 => dbg!(day01::Puzzle::solve(desc, part)),
        2 => dbg!(day02::Puzzle::solve(desc, part)),
        3 => dbg!(day03::Puzzle::solve(desc, part)),
        4 => dbg!(day04::Puzzle::solve(desc, part)),
        5 => dbg!(day05::Puzzle::solve(desc, part)),
        6 => dbg!(day06::Puzzle::solve(desc, part)),
        7 => dbg!(day07::Puzzle::solve(desc, part)),
        8 => dbg!(day08::Puzzle::solve(desc, part)),
        9 => dbg!(day09::Puzzle::solve(desc, part)),
        10 => dbg!(day10::Puzzle::solve(desc, part)),
        11 => dbg!(day11::Puzzle::solve(desc, part)),
        12 => dbg!(day12::Puzzle::solve(desc, part)),
        13 => dbg!(day13::Puzzle::solve(desc, part)),
        14 => dbg!(day14::Puzzle::solve(desc, part)),
        15 => dbg!(day15::Puzzle::solve(desc, part)),
        16 => dbg!(day16::Puzzle::solve(desc, part)),
        17 => dbg!(day17::Puzzle::solve(desc, part)),
        18 => dbg!(day18::Puzzle::solve(desc, part)),
        19 => dbg!(day19::Puzzle::solve(desc, part)),
        // 20 => day20::Puzzle::solve(desc, part),
        // 21 => day21::Puzzle::solve(desc, part),
        // 22 => day22::Puzzle::solve(desc, part),
        // 23 => day23::Puzzle::solve(desc, part),
        // 24 => day24::Puzzle::solve(desc, part),
        // 25 => day25::Puzzle::solve(desc, part),
        _ => dbg!(template::Puzzle::solve(desc, part)),
    };
}
