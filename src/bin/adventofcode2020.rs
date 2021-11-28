use {
    adventofcode::{y2020::*, Description},
    std::env::args,
};

pub fn main() {
    if args().count() == 1 {
        println!("$0 12 1 test1\t12日目のパート1をdata/input-day12-test1.txtを元に実行");
        println!("$0 12 2\t\t12日目のパート2をdata/input-day12.txtを元に実行");
        println!("$0 23 1 -test\t23日目のパート1を（'-test'フラグ付き、入力データなしで）実行");
        println!("$0 23 2 -\t22日目のパート2を（'-'フラグ付き、入力データなしで）実行");
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
    let desc: Description = if let Some(ext) = a.next() {
        Description::FileTag(ext)
    } else {
        Description::None
    };
    match day {
        1 => day01(part, desc),
        2 => day02(part, desc),
        3 => day03(part, desc),
        4 => day04(part, desc),
        5 => day05(part, desc),
        6 => day06(part, desc),
        7 => day07(part, desc),
        8 => day08(part, desc),
        9 => day09(part, desc),
        10 => day10(part, desc),
        11 => day11(part, desc),
        12 => day12(part, desc),
        13 => day13(part, desc),
        14 => day14(part, desc),
        15 => day15(part, desc),
        16 => day16(part, desc),
        17 => day17(part, desc),
        18 => day18(part, desc),
        19 => day19(part, desc),
        20 => day20(part, desc),
        21 => day21(part, desc),
        22 => day22(part, desc),
        23 => day23(part, desc),
        24 => day24(part, desc),
        25 => day25(part, desc),
        _ => template(part, desc),
    };
}
