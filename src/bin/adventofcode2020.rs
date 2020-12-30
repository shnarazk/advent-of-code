use {
    adventofcode2020::{
        day01, day02, day03, day04, day05, day06, day07, day08, day09, day10, day11, day12, day13,
        day14, day15, day16, day17, day18, day19, day20, day21, day22, day23, day24, day25,
        template, Description,
    },
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
        Description::FileTag(ext.to_string())
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
        12 => day12(),
        13 => day13(),
        14 => day14(),
        15 => day15(part, desc),
        16 => day16(part, desc),
        17 => day17(),
        18 => day18(part, desc),
        19 => day19(),
        20 => day20(),
        21 => day21(part, desc),
        22 => day22(part, desc),
        23 => day23(part, desc),
        24 => day24(part, desc),
        25 => day25(part, desc),
        _ => template(part, desc),
    };
}
