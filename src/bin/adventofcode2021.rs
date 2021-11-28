use {
    adventofcode::{y2021::*, Description},
    std::env::args,
};

pub fn main() {
    if args().count() == 1 {
        println!("USAGE:");
        println!(" $0 DD P test1\tDD日目のパートPをdata/2021/input-dayDD-testP.txtを元に実行");
        println!(" $0 DD P\tDD日目のパートPをdata/2021/input-dayDD.txtを元に実行");
        println!(" $0 DD P -test\tDD日目のパートPを（'-test'フラグ付き、入力データなしで）実行");
        println!(" $0 DD P -\tDD日目のパートPを（'-'フラグ付き、入力データなしで）実行");
        println!("option '-test' \t??");
        println!("option '-' \t??");
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
        // _1 => day01(part, desc),
        // _2 => day02(part, desc),
        // _3 => day03(part, desc),
        // _4 => day04(part, desc),
        // _5 => day05(part, desc),
        // _6 => day06(part, desc),
        // _7 => day07(part, desc),
        // _8 => day08(part, desc),
        // _9 => day09(part, desc),
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
