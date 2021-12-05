/// data handling frmework
use std::{fmt::Debug, fs::File, io::prelude::*};

/// IT MUST BE UNDER THE HOOD
#[derive(Clone, Debug, PartialEq)]
pub enum Description {
    FileTag(String),
    TestData(String),
    None,
}

/// IT MUST BE UNDER THE HOOD
#[derive(Debug, PartialEq)]
pub enum Answer<Output1: Sized + Debug + PartialEq, Output2: Sized + Debug + PartialEq> {
    Answers(Output1, Output2),
    Part1(Output1),
    Part2(Output2),
    None,
}

/// A custom error type for errors during reading data file
#[derive(Debug)]
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

/// An alias for `Result<T, ParseError>`
pub type Maybe<T> = Result<T, ParseError>;

/// The standard interface for a data unit which corresponds to a 'block' in an input stream
pub trait TryParse: Debug + Sized {
    /// Parse a block then return `Result<ProblemObject, ParseError>`
    /// ## A typical implementation example
    /// ```
    /// fn parse(s: &str) -> Result<Self, ParseError> {
    ///     let parser: Regex = Regex::new(r"^(down|up) ([0-9]+)$").expect("wrong");
    ///     let segment = parser.captures(s).ok_or(ParseError)?;
    ///     let num: usize = segment[2].parse::<usize>()?;
    ///     match &segment[1] {
    ///         "down" => Ok(Object::Down(num)),
    ///         "up" => Ok(Object::Up(num)),
    ///         _ => Err(ParseError),
    ///     }
    /// }
    /// ```
    fn parse(s: &str) -> Maybe<Self>;
}

impl TryParse for () {
    fn parse(_: &str) -> Maybe<Self> {
        Ok(())
    }
}

impl TryParse for usize {
    fn parse(s: &str) -> Maybe<Self> {
        s.parse::<usize>().map_err(|_| ParseError)
    }
}

impl TryParse for isize {
    fn parse(s: &str) -> Maybe<Self> {
        s.parse::<isize>().map_err(|_| ParseError)
    }
}

impl TryParse for String {
    fn parse(line: &str) -> Maybe<Self> {
        line.is_empty().then(|| line.to_string()).ok_or(ParseError)
    }
}

/// The standard interface for a problem description with solving methods
pub trait AdventOfCode: Debug + Sized {
    type Segment: TryParse + Debug;
    type Output1: Sized + Debug + PartialEq;
    type Output2: Sized + Debug + PartialEq;
    const YEAR: usize;
    const DAY: usize;
    /// delimeter between data blocks
    const DELIMITER: &'static str;
    /// return an initialized setting
    /// ## A typical implementation example
    /// ```
    /// fn default() -> Self {
    ///     Self {
    ///         data: Vec::new(),
    ///         num_data: 0
    ///     }
    /// }
    /// ```
    fn default() -> Self;
    /// read the input, run solver(s), return the results
    fn go(part: usize, desc: Description) {
        dbg!(Self::parse(desc).expect("failed to parse").run(part));
    }
    /// An optional function to handle header section from the contents an input file.
    /// It must return the remanis as `Ok(Some(remains as String))`.
    /// ## A typical implementation example
    /// ```
    /// fn header(&mut self, input: &str) -> Maybe<Option<String>> {
    ///     let parser: Regex = Regex::new(r"^(.+)\n\n((.|\n)+)$").expect("wrong");
    ///     let segment = parser.captures(input).ok_or(ParseError)?;
    ///     for num in segment[1].split(',') {
    ///         self.settings.push(num.parse::<usize>()?);
    ///     }
    ///     Ok(Some(segment[2].to_string()))
    /// }
    /// ```
    fn header(&mut self, _input: &str) -> Maybe<Option<String>> {
        Ok(None)
    }
    /// called by getting a new `Self::Segment` which was generated by `Self::Segment::parse`
    /// ## A typical implementation example
    /// ```
    /// fn insert(&mut self, value: Self::Segment) {
    ///     self.data.push(value);
    ///     self.num_data += 1;
    /// }
    /// ```
    fn insert(&mut self, value: Self::Segment);
    /// An optional function to wrap up initialization.
    /// ## A typical implementation example
    /// ```
    /// fn after_insert(&mut self) {
    ///     self.num_data = self.data.len();
    /// }
    /// ```
    fn after_insert(&mut self) {}
    /// # UNDER THE HOOD
    fn load(desc: Description) -> Maybe<String> {
        fn input_filename(desc: Description, year: usize, day: usize) -> Maybe<String> {
            match desc {
                Description::FileTag(tag) => {
                    Ok(format!("data/{}/input-day{:>02}-{}.txt", year, day, tag))
                }
                Description::None => Ok(format!("data/{}/input-day{:>02}.txt", year, day)),
                _ => Err(ParseError),
            }
        }
        fn load_file(file_name: String) -> Maybe<String> {
            match File::open(&file_name) {
                Ok(mut file) => {
                    let mut contents = String::new();
                    if let Err(e) = file.read_to_string(&mut contents) {
                        panic!("Can't read {}: {:?}", file_name, e);
                    }
                    println!("# loaded {}", &file_name);
                    Ok(contents)
                }
                Err(e) => panic!("Can't read {}: {:?}", file_name, e),
            }
        }
        fn load_data(desc: Description) -> Maybe<String> {
            match desc {
                Description::TestData(s) if s.is_empty() => Err(ParseError),
                Description::TestData(s) => Ok(s),
                _ => Err(ParseError),
            }
        }
        match desc {
            Description::FileTag(_) => load_file(input_filename(desc, Self::YEAR, Self::DAY)?),
            Description::TestData(_) => load_data(desc),
            Description::None => load_file(input_filename(desc, Self::YEAR, Self::DAY)?),
        }
    }
    /// # UNDER THE HOOD.
    /// parse a structured data file, which has some 'blocks' separated with `Self::DELIMITER`
    /// then return `Ok(Self)`.
    fn parse(desc: Description) -> Maybe<Self> {
        let mut instance = Self::default();
        let contents = Self::load(desc)?;
        if let Some(remains) = instance.header(&contents)? {
            for block in remains.split(Self::DELIMITER) {
                instance.insert(Self::Segment::parse(block)?);
            }
        } else {
            for block in contents.split(Self::DELIMITER) {
                instance.insert(Self::Segment::parse(block)?);
            }
        }
        instance.after_insert();
        Ok(instance)
    }
    /// the solver for part1
    /// ## A typical implementation example
    /// ```
    /// fn part1(&mut self) -> Self::Output1 {
    ///     self.data.iter().filter(|x| !x.is_empty()).count()
    /// }
    /// ```
    fn part1(&mut self) -> Self::Output1;
    /// the solver for part1
    /// ## A typical implementation example
    /// ```
    /// fn part2(&mut self) -> Output2 {
    ///     self.data.iter().filter(|x| !x.is_empty()).map(|x| x * x).sum()
    /// }
    /// ```
    fn part2(&mut self) -> Self::Output2;
    /// # UNDER THE HOOD
    fn run(&mut self, part: usize) -> Answer<Self::Output1, Self::Output2> {
        match part {
            0 => {
                println!("# Advent of Code {}: day {}, part 1", Self::YEAR, Self::DAY);
                let ans1 = self.part1();
                println!("# Advent of Code {}: day {}, part 2", Self::YEAR, Self::DAY);
                let ans2 = self.part2();
                Answer::Answers(ans1, ans2)
            }
            1 => {
                println!("# Advent of Code {}: day {}, part 1", Self::YEAR, Self::DAY);
                Answer::Part1(self.part1())
            }
            2 => {
                println!("# Advent of Code {}: day {}, part 2", Self::YEAR, Self::DAY);
                Answer::Part2(self.part2())
            }
            _ => Answer::None,
        }
    }
}
