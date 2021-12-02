use {
    adventofcode::{template, y2021::*, Description},
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
        0 => day00::go(part, desc),
        1 => day01::go(part, desc),
        2 => day02::go(part, desc),
        3 => day03::go(part, desc),
        4 => day04::go(part, desc),
        5 => day05::go(part, desc),
        6 => day06::go(part, desc),
        7 => day07::go(part, desc),
        8 => day08::go(part, desc),
        9 => day09::go(part, desc),
        // 10 => day10::go(part, desc),
        // 11 => day11::go(part, desc),
        // 12 => day12::go(part, desc),
        // 13 => day13::go(part, desc),
        // 14 => day14::go(part, desc),
        // 15 => day15::go(part, desc),
        // 16 => day16::go(part, desc),
        // 17 => day17::go(part, desc),
        // 18 => day18::go(part, desc),
        // 19 => day19::go(part, desc),
        // 20 => day20::go(part, desc),
        // 21 => day21::go(part, desc),
        // 22 => day22::go(part, desc),
        // 23 => day23::go(part, desc),
        // 24 => day24::go(part, desc),
        // 25 => day25::go(part, desc),
        _ => template::go(part, desc),
    };
}
