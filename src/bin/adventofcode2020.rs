use {
    adventofcode2020::{
        day01,
        day02,
        day03,
        day04,
        day05,
        day06,
        day07,
        day08,
        day09,
        day10,
        day11,
        day12,
        day13,
        day14,
        day15,
        day16,
        day17,
        day18,
        day19,
        day20,
        day21,
        day22,
        day23,
        day24,
        day25,
    },
    std::env::args,
};

pub fn main() {
    match args()
        .last()
        .unwrap_or("1".to_string())
        .parse::<usize>()
        .unwrap_or(1)
    {
        1 => day01(),
        2 => day02(),
        3 => day03(),
        4 => day04(),
        5 => day05(),
        6 => day06(),
        7 => day07(),
        8 => day08(),
        9 => day09(),
        10 => day15(),
        11 => day11(),
        12 => day12(),
        13 => day13(),
        14 => day14(),
        15 => day15(),
        16 => day16(),
        17 => day17(),
        18 => day18(),
        19 => day19(),
        20 => day20(),
        21 => day21(),
        22 => day22(),
        23 => day23(),
        24 => day24(),
        25 => day25(),
        _ => (),
    }
}
