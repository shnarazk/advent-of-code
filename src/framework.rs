//! data handling frmework
pub use aoc_macro::{aoc, aoc_at};
use {
    crate::color,
    clap::Parser,
    once_cell::sync::OnceCell,
    std::{borrow::Borrow, fmt, fs::File, io::prelude::*},
};

#[derive(Clone, Debug, Parser)]
#[command(author, version, about, long_about = None)]
pub struct ConfigAoC {
    /// Target year like 2023
    #[arg(long)]
    pub bench: Option<usize>,
    /// Target year like 2023
    #[arg(short, long, default_value_t = 2023)]
    pub year: usize,
    #[arg(short, long, default_value_t = 3)]
    pub part: usize,
    /// Target day like 1
    pub day: Option<usize>,
    /// Extra data filename segment like "test1" for "input-dayXX-test1.txt"
    pub alt: Option<String>,
    /// serialize as JSON format
    #[arg(short, long)]
    pub serialize: bool,
}

static CONFIG: OnceCell<ConfigAoC> = OnceCell::new();

/// IT MUST BE UNDER THE HOOD
#[derive(Clone, fmt::Debug, Eq, PartialEq)]
pub enum Description {
    FileTag(String),
    TestData(String),
    None,
}

impl fmt::Display for Description {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl Description {
    /// return data file name
    fn data_filename(&self, year: usize, day: usize) -> Result<String, ParseError> {
        match self {
            Description::FileTag(tag) => Ok(format!("data/{year}/input-day{day:>02}-{tag}.txt")),
            Description::None => Ok(format!("data/{year}/input-day{day:>02}.txt")),
            Description::TestData(_) => Ok("A test input".to_string()),
        }
    }
    /// return the file name for serialization
    fn serialization_filename(&self, year: usize, day: usize) -> Result<String, ParseError> {
        match self {
            Description::FileTag(tag) => Ok(format!("tmp/{year}/day{day:>02}-{tag}.json")),
            Description::None => Ok(format!("tmp/{year}/day{day:>02}.json")),
            Description::TestData(_) => Ok("test.json".to_string()),
        }
    }
}

static DATA_SOURCE: OnceCell<Description> = OnceCell::new();

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

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "End of Stream")
    }
}

impl std::error::Error for ParseError {}

/// The standard interface for a problem description with solving methods
pub trait AdventOfCode: fmt::Debug + Default {
    type Output1: fmt::Debug + PartialEq;
    type Output2: fmt::Debug + PartialEq;
    const YEAR: usize;
    const DAY: usize;
    /// delimeter between data blocks
    const DELIMITER: &'static str;
    /// An optional function to handle header section from the contents an input file.
    /// It must return the remanis as `Ok(Some(remains as String))`.
    /// ## A typical implementation example
    /// ```ignore
    /// fn header(&mut self, input: String) -> Result<String, ParseError> {
    ///     let parser: Regex = Regex::new(r"^(.+)\n\n((.|\n)+)$").expect("wrong");
    ///     let segment = parser.captures(input).ok_or(ParseError)?;
    ///     for num in segment[1].split(',') {
    ///         self.settings.push(num.parse::<usize>()?);
    ///     }
    ///     Ok(Some(segment[2].to_string()))
    /// }
    /// ```
    fn header(&mut self, input: String) -> Result<String, ParseError> {
        Ok(input)
    }
    /// called by getting a new data block
    /// ## A typical implementation example
    /// ```ignore
    /// fn insert(&mut self, block: &str) -> Result<(), ParseError> {
    ///     let parser: Regex = Regex::new(r"^(down|up) ([0-9]+)$").expect("wrong");
    ///     let segment = parser.captures(s).ok_or(ParseError)?;
    ///     let num: usize = segment[2].parse::<usize>()?;
    ///     let segment = match &segment[1] {
    ///         "down" => Object::Down(num),
    ///         "up" => Object::Up(num),
    ///         _ => return;
    ///     }
    ///     self.data.push(segment);;
    ///     self.num_data += 1;
    ///     Ok(())
    /// }
    /// ```
    fn insert(&mut self, s: &str) -> Result<(), ParseError>;
    /// An optional function to wrap up initialization.
    /// ## A typical implementation example
    /// ```ignore
    /// fn end_of_data(&mut self) {
    ///     self.num_data = self.data.len();
    /// }
    /// ```
    fn end_of_data(&mut self) {}
    /// # UNDER THE HOOD
    fn load(description: impl Borrow<Description>) -> Result<String, ParseError> {
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
        fn load_data(desc: &Description) -> Result<String, ParseError> {
            match desc {
                Description::TestData(s) => Ok(s.to_string()),
                _ => Err(ParseError),
            }
        }
        let desc = description.borrow();
        match desc {
            Description::FileTag(_) => load_file(desc.data_filename(Self::YEAR, Self::DAY)?),
            Description::TestData(_) => load_data(desc),
            Description::None => load_file(desc.data_filename(Self::YEAR, Self::DAY)?),
        }
    }
    /// # UNDER THE HOOD.
    /// parse a structured data file, which has some 'blocks' separated with `Self::DELIMITER`
    /// then return `Ok(Self)`.
    fn parse(config: ConfigAoC) -> Result<Self, ParseError> {
        let description = match config.alt {
            Some(ext) if ext == "-" => Description::TestData("".to_string()),
            Some(ext) => Description::FileTag(ext.to_string()),
            None => Description::None,
        };
        let mut instance = Self::default();
        let contents = Self::load(description)?;
        let remains = instance.header(contents)?;
        for block in remains.split(Self::DELIMITER) {
            if !block.is_empty() {
                instance.insert(block)?;
            }
        }
        instance.end_of_data();
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
    /// the solver for part1
    /// ## A typical implementation example
    /// ```ignore
    /// fn part2(&mut self) -> Output2 {
    ///     self.data.iter().filter(|x| !x.is_empty()).map(|x| x * x).sum()
    /// }
    /// ```
    fn part2(&mut self) -> Self::Output2;
    /// returns String by serialization in JSON format
    fn serialize(&self) -> Option<String> {
        None
    }
    /// write serialization data generated by `serialize`
    fn dump(&self) {
        let Some(config) = CONFIG.get() else {
            return;
        };
        let Some(desc) = DATA_SOURCE.get() else {
            return;
        };
        if !config.serialize {
            return;
        }
        let Ok(output) = desc.serialization_filename(Self::YEAR, Self::DAY) else {
            return;
        };
        if let Some(json) = self.serialize() {
            let mut file = File::create(&output).expect("fail to open");
            writeln!(file, "{}", json).expect("fail to save");
            println!(
                "{}# write JSON data on {}{}",
                color::MAGENTA,
                output,
                color::RESET,
            );
        };
    }
    /// # UNDER THE HOOD
    /// read the input, run solver(s), return the results
    fn solve(config: ConfigAoC) -> Answer<Self::Output1, Self::Output2> {
        let description = match config.clone().alt {
            Some(ext) if ext == "-" => Description::TestData("".to_string()),
            Some(ext) => Description::FileTag(ext.to_string()),
            None => Description::None,
        };

        if CONFIG.get().is_none() {
            CONFIG.set(config.clone()).expect("fail to store config");
        }
        if DATA_SOURCE.get().is_none() {
            DATA_SOURCE
                .set(description.clone())
                .expect("fail to store config");
        }
        let input = description
            .data_filename(Self::YEAR, Self::DAY)
            .expect("no input");
        let parse_error = format!("{}failed to parse{}", color::RED, color::RESET);
        match config.part {
            0 => {
                assert!(config.serialize);
                Self::parse(config).expect(&parse_error).dump();
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
                Answer::Part1(Self::parse(config).expect(&parse_error).part1())
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
                Answer::Part2(Self::parse(config).expect(&parse_error).part2())
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
                let ans1 = Self::parse(config.clone()).expect(&parse_error).part1();
                let ans2 = Self::parse(config).expect(&parse_error).part2();
                Answer::Answers(ans1, ans2)
            }
            _ => Answer::None,
        }
    }
    fn get_config() -> &'static ConfigAoC {
        CONFIG.get().unwrap()
    }
    fn get_data_source() -> &'static Description {
        DATA_SOURCE.get().unwrap()
    }
}
