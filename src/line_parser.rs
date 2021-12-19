//! misc implementations of string-to-object parsers
use {crate::framework::ParseError, lazy_static::lazy_static, regex::Regex};

/// parse a line like '0,1,2,3,4' (delimiter == ',') after trimming it
/// ```
/// use adventofcode::{framework::ParseError, line_parser};
/// assert_eq!(line_parser::to_usizes("0,1,8,9", ','), Ok(vec![0, 1, 8, 9]));
/// assert_eq!(line_parser::to_usizes("100 200", ' '), Ok(vec![100, 200]));
/// assert_eq!(line_parser::to_usizes("", ','), Err(ParseError));
/// ```
pub fn to_usizes(line: &str, delimiter: char) -> Result<Vec<usize>, ParseError> {
    let result = line
        .trim()
        .split(delimiter)
        .filter(|s| !s.is_empty())
        .map(|n| n.parse::<usize>().expect("-"))
        .collect::<Vec<_>>();
    if result.is_empty() {
        Err(ParseError)
    } else {
        Ok(result)
    }
}

/// parse a line like '-312'
/// ```
/// use adventofcode::{framework::ParseError, line_parser};
/// assert_eq!(line_parser::to_isize("-0189"), Ok(-0189));
/// assert_eq!(line_parser::to_isize("0"), Ok(0));
/// assert_eq!(line_parser::to_isize("448"), Ok(448));
/// ```
pub fn to_isize(line: &str) -> Result<isize, ParseError> {
    if line.starts_with('-') {
        Ok(-line.trim_matches('-').parse::<isize>()?)
    } else {
        Ok(line.parse::<isize>()?)
    }
}

/// parse a line like '01234' after trimming it
/// ```
/// use adventofcode::{framework::ParseError, line_parser};
/// assert_eq!(line_parser::to_digits("0189"), Ok(vec![0, 1, 8, 9]));
/// assert_eq!(line_parser::to_digits("0"), Ok(vec![0]));
/// assert_eq!(line_parser::to_digits(""), Err(ParseError));
/// ```
pub fn to_digits(line: &str) -> Result<Vec<usize>, ParseError> {
    let result = line
        .trim()
        .chars()
        .map(|n| match n {
            '0' => 0,
            '1' => 1,
            '2' => 2,
            '3' => 3,
            '4' => 4,
            '5' => 5,
            '6' => 6,
            '7' => 7,
            '8' => 8,
            '9' => 9,
            _ => panic!("wrong digit"),
        })
        .collect::<Vec<usize>>();
    if result.is_empty() {
        Err(ParseError)
    } else {
        Ok(result)
    }
}

/// parse a line like '010101010' after trimming it
/// ```
/// use adventofcode::{framework::ParseError, line_parser};
/// assert_eq!(line_parser::to_binaries("0"), Ok(vec![false]));
/// assert_eq!(line_parser::to_binaries("0011"), Ok(vec![false, false, true, true]));
/// assert_eq!(line_parser::to_binaries(""), Err(ParseError));
/// ```
pub fn to_binaries(line: &str) -> Result<Vec<bool>, ParseError> {
    lazy_static! {
        static ref PARSER: Regex = Regex::new(r"^[01]+$").expect("wrong");
    }
    let segment = PARSER.captures(line.trim()).ok_or(ParseError)?;
    Ok(segment[0].chars().map(|s| s == '1').collect::<Vec<bool>>())
}

/// parse a line like 'ewnswss' after trimming it
/// ```
/// use adventofcode::{framework::ParseError, line_parser};
/// assert_eq!(line_parser::to_chars("0"), Ok(vec!['0']));
/// assert_eq!(line_parser::to_chars("0aA-"), Ok(vec!['0', 'a', 'A', '-']));
/// assert_eq!(line_parser::to_chars(""), Ok(vec![]));
/// ```
pub fn to_chars(line: &str) -> Result<Vec<char>, ParseError> {
    Ok(line.trim().chars().collect::<Vec<_>>())
}
