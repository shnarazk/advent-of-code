use {
    adventofcode2020::{
        day01, day02, day03, day04, day05, day06, day07, day08, day09, day10, day11, day12, day13,
        day14, day15, day16, day17, day18, day19, day20, day21, day22, day23, day24, day25,
        template, Description,
    },
    std::{env::args, fs::File, io::prelude::*},
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
    let test = a.next();
    let desc: Description = if let Some(ref ext) = test {
        Description::FileTag(ext.to_string())
    } else {
        Description::None
    };
    let input_data = if [1, 2, 3, 4, 5, 6, 7, 10, 16, 18, 21, 22, 23, 24, 25].contains(&day) {
        "".to_string()
    } else if let Some(ref ext) = test {
        if ext.starts_with('-') {
            ext.to_string()
        } else {
            let f = format!("input-day{:>02}-{}.txt", day, ext);
            read_input(&f).unwrap_or_else(|| panic!("Can't read {}", f))
        }
    } else {
        let f = format!("input-day{:>02}.txt", day);
        read_input(&f).unwrap_or_else(&|| panic!("Can't read {}", f))
    };
    match day {
        1 => day01(part, desc),
        2 => day02(part, desc),
        3 => day03(part, desc),
        4 => day04(part, desc),
        5 => day05(part, desc),
        6 => day06(part, desc),
        7 => day07(part, desc),
        8 => day08(part, input_data),
        9 => day09(part, input_data),
        10 => day10(part, desc),
        11 => day11(),
        12 => day12(),
        13 => day13(),
        14 => day14(),
        15 => day15(),
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

fn read_input(fname: &str) -> Option<String> {
    match File::open(format!("data/{}", fname)) {
        Ok(mut file) => {
            let mut contents = String::new();
            if let Err(e) = file.read_to_string(&mut contents) {
                panic!("Can't read {}: {:?}", fname, e);
            }
            Some(contents)
        }
        Err(e) => panic!("Can't read {}: {:?}", fname, e),
    }
}
