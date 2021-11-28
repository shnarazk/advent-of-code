use {
    adventofcode::{template::template, y2021::*, Description},
    std::env::args,
};

pub fn main() {
    if args().count() == 1 {
        println!("USAGE:");
        println!(" $0 DD\t\tDD日目のパート{{1, 2}}をdata/2021/input-dayDD.txtを入力として実行");
        println!(" $0 DD P\tDD日目のパートPをdata/2021/input-dayDD.txtを入力として実行");
        println!(" $0 DD P TTT\tDD日目のパートPをdata/2021/input-dayDD-TTT.txtを入力として実行");
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
        0_ => day00::go(part, desc),
        // 1_ => day01(part, desc),
        // 2_ => day02(part, desc),
        // 3_ => day03(part, desc),
        // 4_ => day04(part, desc),
        // 5_ => day05(part, desc),
        // 6_ => day06(part, desc),
        // 7_ => day07(part, desc),
        // 8_ => day08(part, desc),
        // 9_ => day09(part, desc),
        // 10 => day10(part, desc),
        // 11 => day11(part, desc),
        // 12 => day12(part, desc),
        // 13 => day13(part, desc),
        // 14 => day14(part, desc),
        // 15 => day15(part, desc),
        // 16 => day16(part, desc),
        // 17 => day17(part, desc),
        // 18 => day18(part, desc),
        // 19 => day19(part, desc),
        // 20 => day20(part, desc),
        // 21 => day21(part, desc),
        // 22 => day22(part, desc),
        // 23 => day23(part, desc),
        // 24 => day24(part, desc),
        // 25 => day25(part, desc),
        _ => template(part, desc),
    };
}
