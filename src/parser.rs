//! misc implementations of string-to-object parsers

#![cfg(any(feature = "y2024", feature = "y2023"))]
use {
    crate::framework::*,
    winnow::{
        ascii::{dec_uint, space0},
        combinator::{repeat, separated},
        token::one_of,
        PResult, Parser,
    },
};

fn parse_usize(str: &mut &str) -> PResult<usize> {
    let a: u64 = dec_uint.parse_next(str)?;
    Ok(a as usize)
}

/// Parse a line like '0,1,2,3,40' (delimiter == ',') after trimming it.
/// If delimiter is '\n', then the real delimiter becomes `&[' ', '\t']`
/// If delimiter is '\t', then the real delimiter becomes `&[' ', '\t', ',']`
/// ```
/// use adventofcode::{framework::ParseError, parser};
/// assert_eq!(parser::to_usizes("0,1,8,9", &[',']), Ok(vec![0, 1, 8, 9]));
/// assert_eq!(parser::to_usizes("100 200", &[' ']), Ok(vec![100, 200]));
/// assert_eq!(parser::to_usizes("100  200  300", &[' ']), Ok(vec![100, 200, 300]));
/// assert_eq!(parser::to_usizes("100, 200   300", &[',', ' ']), Ok(vec![100, 200, 300]));
/// assert_eq!(parser::to_usizes("", &[',']), Err(ParseError));
/// ```
pub fn to_usizes(line: &str, delimiters: &[char]) -> Result<Vec<usize>, ParseError> {
    fn parse(s: &mut &str, delimiters: &[char]) -> PResult<Vec<usize>> {
        let _ = space0.parse_next(s)?;
        Ok(separated(
            1..,
            parse_usize,
            repeat(1.., one_of(delimiters)).fold(|| (), |_, _| ()),
        )
        .parse_next(s)?)
    }
    let s = line.to_string();
    let p = &mut s.as_str();
    Ok(parse(p, delimiters)?)
}

/*
/// Sprit and parse a line like '0, 1, 2, 3, 40' with delimiter `&[',', ' ']`.
/// ```
/// use adventofcode::{framework::ParseError, line_parser};
/// assert_eq!(line_parser::to_usizes_spliting_with("100  200  300", &[' ']), Ok(vec![100, 200, 300]));
/// assert_eq!(line_parser::to_usizes_spliting_with("100, 200, 300", &[',', ' ']), Ok(vec![100, 200, 300]));
/// ```
pub fn to_usizes_spliting_with(line: &str, delimiter: &[char]) -> Result<Vec<usize>, ParseError> {
    let result = line
        .trim()
        .split(delimiter)
        .filter(|s| !s.is_empty())
        .map(|n| n.parse::<usize>().expect("An invalid input as usize"))
        .collect::<Vec<_>>();
    if result.is_empty() {
        Err(ParseError)
    } else {
        Ok(result)
    }
}

/// parse a line like '312'
/// ```
/// use adventofcode::{framework::ParseError, line_parser};
/// assert_eq!(line_parser::to_isize("-0189"), Ok(-189));
/// assert_eq!(line_parser::to_isize("0"), Ok(0));
/// assert_eq!(line_parser::to_isize("448"), Ok(448));
/// ```
pub fn to_usize(line: &str) -> Result<usize, ParseError> {
    if line.starts_with('-') {
        Ok(line.trim_matches('-').parse::<usize>()?)
    } else {
        Ok(line.parse::<usize>()?)
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

/// parse a line like '0,-1,2,-3,40' (delimiter == ',') after trimming it
/// If delimiter is '\n', then the real delimiter becomes `&[' ', '\t']`
/// If delimiter is '\t', then the real delimiter becomes `&[' ', '\t', ',']`
/// ```
/// use adventofcode::{framework::ParseError, line_parser};
/// assert_eq!(line_parser::to_isizes("0,-1,8,-9", ','), Ok(vec![0, -1, 8, -9]));
/// assert_eq!(line_parser::to_isizes("-100 200", ' '), Ok(vec![-100, 200]));
/// assert_eq!(line_parser::to_isizes("-100  200  -1", '\n'), Ok(vec![-100, 200, -1]));
/// assert_eq!(line_parser::to_isizes("-100, 200  -1", '\t'), Ok(vec![-100, 200, -1]));
/// assert_eq!(line_parser::to_isizes("", ','), Err(ParseError));
/// ```
pub fn to_isizes(line: &str, delimiter: char) -> Result<Vec<isize>, ParseError> {
    let result = match delimiter {
        '\n' => line
            .trim()
            .split(&[' ', '\t'])
            .filter(|s| !s.is_empty())
            .map(|n| n.parse::<isize>().expect("An invalid input as isize"))
            .collect::<Vec<_>>(),
        '\t' => line
            .trim()
            .split(&[' ', '\t', ','])
            .filter(|s| !s.is_empty())
            .map(|n| n.parse::<isize>().expect("An invalid input as isize"))
            .collect::<Vec<_>>(),
        _ => line
            .trim()
            .split(delimiter)
            .filter(|s| !s.is_empty())
            .map(|n| n.parse::<isize>().expect("An invalid input as isize"))
            .collect::<Vec<_>>(),
    };
    if result.is_empty() {
        Err(ParseError)
    } else {
        Ok(result)
    }
}

/// Sprit and parse a line like '0, -1, 2, -3, 40' with delimiter `&[',', ' ']`.
/// ```
/// use adventofcode::{framework::ParseError, line_parser};
/// assert_eq!(line_parser::to_isizes_spliting_with("-1  2  -3", &[' ']), Ok(vec![-1, 2, -3]));
/// assert_eq!(line_parser::to_isizes_spliting_with("-1, 2, -3", &[',', ' ']), Ok(vec![-1, 2, -3]));
/// ```
pub fn to_isizes_spliting_with(line: &str, delimiter: &[char]) -> Result<Vec<isize>, ParseError> {
    let result = line
        .trim()
        .split(delimiter)
        .filter(|s| !s.is_empty())
        .map(|n| n.parse::<isize>().expect("An invalid input as usize"))
        .collect::<Vec<_>>();
    if result.is_empty() {
        Err(ParseError)
    } else {
        Ok(result)
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
    let parser = regex!(r"^[01]+$");
    let segment = parser.captures(line.trim()).ok_or(ParseError)?;
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
*/
