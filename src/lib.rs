#![feature(portable_simd)]
pub mod array;
pub mod color;
pub mod framework;
pub mod geometric;
pub mod math;
pub mod parser;
pub mod rect;

#[cfg(feature = "y2015")]
pub mod y2015;
#[cfg(feature = "y2016")]
pub mod y2016;
#[cfg(feature = "y2017")]
pub mod y2017;
#[cfg(feature = "y2018")]
pub mod y2018;
#[cfg(feature = "y2019")]
pub mod y2019;
#[cfg(feature = "y2020")]
pub mod y2020;
#[cfg(feature = "y2021")]
pub mod y2021;
#[cfg(feature = "y2022")]
pub mod y2022;
#[cfg(feature = "y2023")]
pub mod y2023;
#[cfg(feature = "y2024")]
pub mod y2024;
#[cfg(feature = "y2025")]
pub mod y2025;

pub use aoc_macro::aoc_arms;

///
/// ```
/// use adventofcode::progress;
///   for i in 0..100 {
///       progress!(i);
///       std::thread::sleep(std::time::Duration::from_millis(20));
///   }
///
/// ```
#[macro_export]
macro_rules! progress {
    ($val: expr) => {{
        print!(
            "\x1B[1A\n\x1B[0J\x1B[48;2;220;220;220m\x1B[38;2;20;100;200m{}\x1B[0m\x1B[1G",
            $val
        );
    }};
}

#[macro_export]
macro_rules! progress_picture {
    ($val: expr) => {{
        let rows = $val.chars().filter(|c| *c == '\n').count() + 1;
        print!(
            "\x1B[{}A\n\x1B[0J\x1B[48;2;220;220;220m\x1B[38;2;20;100;200m{}\x1B[0m\x1B[1G",
            rows, $val
        );
    }};
}
