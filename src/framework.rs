//! data handling framework
pub use aoc_macro::{aoc, aoc_at};

use {
    crate::color,
    clap::Parser,
    std::sync::OnceLock,
    std::{
        fmt,
        fs::File,
        io::prelude::*,
        path::{Path, PathBuf},
    },
};

pub const JSON_DUMP_DIR: &str = "misc";
pub const DATA_DIR: &str = "data";

#[derive(Clone, Debug, Default, Parser)]
#[command(author, version, about, long_about = None)]
pub struct ConfigAoC {
    /// Dump all execution times to misc/YEAR/execution_time.json
    #[arg(short, long)]
    pub bench: bool,
    /// Target year like 2023
    #[arg(short, long, default_value_t = 2024)]
    pub year: usize,
    /// Target section, 0 is used for dumping a problem as JSON
    #[arg(short, long, default_value_t = 3)]
    pub part: usize,
    /// Target day like 1
    pub day: Option<usize>,
    /// Extra data filename segment like "test1" for "input-day##-test1.txt"
    pub alt: Option<String>,
    /// activate 'dump' function for JSON serialization
    #[arg(short, long)]
    pub serialize: bool,
}
impl ConfigAoC {
    /// return data file name
    fn data_filename(&self, year: usize, day: usize) -> Result<String, ParseError> {
        match &self.alt {
            Some(ext) if ext == "-" => Ok("A test input".to_string()),
            Some(ext) => Ok(format!("{DATA_DIR}/{year}/input-day{day:>02}-{ext}.txt")),
            None => Ok(format!("{DATA_DIR}/{year}/input-day{day:>02}.txt")),
        }
    }
    /// return the file name for serialization
    fn serialization_filename(&self, year: usize, day: usize) -> Result<String, ParseError> {
        match &self.alt {
            Some(ext) if ext == "-" => Ok("test.json".to_string()),
            Some(ext) => Ok(format!("{JSON_DUMP_DIR}/{year}/day{day:>02}-{ext}.json")),
            None => Ok(format!("{JSON_DUMP_DIR}/{year}/day{day:>02}.json")),
        }
    }
    pub fn serialization_path(
        &self,
        year: usize,
        day: usize,
        key: &str,
    ) -> Result<PathBuf, ParseError> {
        match &self.alt {
            Some(ext) if ext == "-" => Ok(PathBuf::from("test.json")),
            Some(ext) => Ok(PathBuf::from(format!(
                "{JSON_DUMP_DIR}/{year}/day{day:>02}-{ext}-{key}"
            ))),
            None => Ok(PathBuf::from(format!(
                "{JSON_DUMP_DIR}/{year}/day{day:>02}-{key}"
            ))),
        }
    }
}

static CONFIG: OnceLock<ConfigAoC> = OnceLock::new();

/// IT MUST BE UNDER THE HOOD
#[derive(Debug, Eq, PartialEq)]
pub enum Answer<Output1: Sized + fmt::Debug + PartialEq, Output2: Sized + fmt::Debug + PartialEq> {
    Answers(Output1, Output2),
    Part1(Output1),
    Part2(Output2),
    Dump,
    None,
}

impl<O1, O2> fmt::Display for Answer<O1, O2>
where
    O1: fmt::Debug + Eq,
    O2: fmt::Debug + Eq,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Answer::Answers(o1, o2) => write!(f, "Answers: {o1:?}, {o2:?}"),
            Answer::Part1(o) => write!(f, "Part1: {o:?}"),
            Answer::Part2(o) => write!(f, "Part2: {o:?}"),
            Answer::Dump => write!(f, ""),
            Answer::None => write!(f, "No answer"),
        }
    }
}

/// A custom error type for errors during reading data file
#[derive(Debug, Eq, PartialEq)]
pub struct ParseError;

impl std::convert::From<std::num::ParseIntError> for ParseError {
    fn from(_: std::num::ParseIntError) -> Self {
        ParseError
    }
}

impl<T> std::convert::From<winnow::error::ErrMode<T>> for ParseError {
    fn from(_: winnow::error::ErrMode<T>) -> Self {
        ParseError
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "End of Stream")
    }
}

impl std::error::Error for ParseError {}

/// The standard interface for a problem description with solving methods
pub trait AdventOfCode: fmt::Debug + Clone + Default {
    type Output1: fmt::Debug + PartialEq;
    type Output2: fmt::Debug + PartialEq;
    const YEAR: usize;
    const DAY: usize;
    /// Parse all from the contents an input file then some post-processing.
    /// ## A typical implementation example
    /// ```ignore
    /// fn prepare(&mut self, input: &str) -> Result<(), ParseError> {
    ///     self.line = parser::parse(&mut input);
    ///     Ok(())
    /// }
    /// ```
    fn prepare(&mut self, mut _input: &str) -> Result<(), ParseError> {
        Ok(())
    }
    /// # UNDER THE HOOD
    fn load(config: ConfigAoC) -> Result<String, ParseError> {
        fn load_file(file_name: String) -> Result<String, ParseError> {
            match File::open(&file_name) {
                Ok(mut file) => {
                    let mut contents = String::new();
                    if let Err(e) = file.read_to_string(&mut contents) {
                        panic!("Can't read {file_name}: {e:?}");
                    }
                    // println!("# loaded {}", &file_name);
                    Ok(contents)
                }
                Err(e) => panic!("Can't read {file_name}: {e:?}"),
            }
        }
        // fn load_data(desc: &Description) -> Result<String, ParseError> {
        //     match desc {
        //         Description::TestData(s) => Ok(s.to_string()),
        //         _ => Err(ParseError),
        //     }
        // }
        load_file(config.data_filename(Self::YEAR, Self::DAY)?)
    }
    /// # UNDER THE HOOD.
    /// parse a structured data file, which has some 'blocks' separated with `Self::DELIMITER`
    /// then return `Ok(Self)`.
    fn build(config: ConfigAoC) -> Result<Self, ParseError> {
        let mut instance = Self::default();
        let contents = Self::load(config)?;
        instance.prepare(contents.as_str())?;
        Ok(instance)
    }
    /// the solver for part1
    /// ## A typical implementation example
    /// ```ignore
    /// fn part1(&mut self) -> Self::Output1 {
    ///     self.data.iter().filter(|x| !x.is_empty()).count()
    /// }
    /// ```
    fn part1(&mut self) -> Self::Output1;
    /// the solver for part2
    /// ## A typical implementation example
    /// ```ignore
    /// fn part2(&mut self) -> Output2 {
    ///     self.data.iter().filter(|x| !x.is_empty()).map(|x| x * x).sum()
    /// }
    /// ```
    fn part2(&mut self) -> Self::Output2;
    /// returns `String` by serialization in JSON format
    ///
    /// ```ignore
    /// fn serialize(&mut self) -> Option<String> {
    ///      serde_json::to_string(self).ok()
    /// }
    /// ```
    fn serialize(&self) -> Option<String> {
        None
    }
    /// # UNDER THE HOOD
    /// write serialization data generated by `serialize`
    fn dump(&self) {
        let Some(config) = CONFIG.get() else {
            return;
        };
        if !config.serialize {
            return;
        }
        let Ok(output) = config.serialization_filename(Self::YEAR, Self::DAY) else {
            return;
        };
        if let Some(json) = self.serialize() {
            let dir = Path::new(&output).parent().unwrap();
            if !dir.exists() {
                std::fs::create_dir_all(dir)
                    .unwrap_or_else(|_| panic!("fail to create a directory {dir:?}"));
            }
            let mut file =
                File::create(&output).unwrap_or_else(|_| panic!("fail to open {output}"));
            writeln!(file, "{json}").expect("fail to save");
            println!(
                "{}# write JSON data on {}{}",
                color::MAGENTA,
                output,
                color::RESET,
            );
        };
    }
    /// write the given contents to a file specified by the key under misc directory.
    fn dump_to<S: AsRef<str>>(&self, key: &str, contents: S) {
        let config = self.get_config();
        if let Ok(path) = config.serialization_path(Self::YEAR, Self::DAY, key) {
            let dir = std::path::Path::new(&path).parent().unwrap();
            if !dir.exists() {
                std::fs::create_dir_all(dir)
                    .unwrap_or_else(|_| panic!("fail to create a directory {dir:?}"));
            }
            let mut file =
                std::fs::File::create(&path).unwrap_or_else(|_| panic!("fail to open {path:?}"));
            writeln!(file, "{:?}", contents.as_ref()).expect("fail to save");
            println!("{}# write {:?}{}", color::MAGENTA, path, color::RESET,);
        }
    }
    /// # UNDER THE HOOD
    /// read the input, run solver(s), return the results
    fn solve(config: ConfigAoC) -> Answer<Self::Output1, Self::Output2> {
        if CONFIG.get().is_none() {
            CONFIG.set(config.clone()).expect("fail to store config");
        }
        let input = config
            .data_filename(Self::YEAR, Self::DAY)
            .expect("no input");
        let parse_error = format!("{}failed to parse{}", color::RED, color::RESET);
        match config.part {
            0 => {
                assert!(config.serialize);
                Self::build(config).expect(&parse_error).dump();
                Answer::Dump
            }
            1 => {
                println!(
                    "{}# year: {}, day: {}, part: 1, input: {}{}",
                    color::GREEN,
                    Self::YEAR,
                    Self::DAY,
                    input,
                    color::RESET,
                );
                Answer::Part1(Self::build(config).expect(&parse_error).part1())
            }
            2 => {
                println!(
                    "{}# year: {}, day: {}, part: 2, input: {}{}",
                    color::GREEN,
                    Self::YEAR,
                    Self::DAY,
                    input,
                    color::RESET,
                );
                Answer::Part2(Self::build(config).expect(&parse_error).part2())
            }
            3 => {
                println!(
                    "{}# year: {}, day: {}, input: {}{}",
                    color::GREEN,
                    Self::YEAR,
                    Self::DAY,
                    input,
                    color::RESET,
                );
                let solver = Self::build(config.clone()).expect(&parse_error);
                let ans1 = solver.clone().part1();
                let ans2 = solver.clone().part2();
                Answer::Answers(ans1, ans2)
            }
            _ => Answer::None,
        }
    }
    fn get_config(&self) -> &'static ConfigAoC {
        CONFIG.get().unwrap()
    }
}
