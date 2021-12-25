pub mod framework;
pub mod geometric;
pub mod line_parser;
#[cfg(feature = "y2020")]
pub mod y2020;
#[cfg(feature = "y2021")]
pub mod y2021;
// #[cfg(feature = "y2019")]
// pub mod y2019;
// #[cfg(feature = "y2018")]
// pub mod y2018;
// #[cfg(feature = "y2017")]
// pub mod y2017;
// #[cfg(feature = "y2016")]
// pub mod y2016;
#[cfg(feature = "y2015")]
pub mod y2015;

pub use aoc_macro::aoc_arms;
pub use framework::Description;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const RED: &str = "\x1B[001m\x1B[031m";
pub const GREEN: &str = "\x1B[001m\x1B[032m";
pub const BLUE: &str = "\x1B[001m\x1B[034m";
pub const MAGENTA: &str = "\x1B[001m\x1B[035m";
pub const RESET: &str = "\x1B[000m";
