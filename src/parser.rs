//! misc implementations of string-to-object parsers
use {
    crate::framework::*,
    winnow::{
        ascii::{dec_int, dec_uint, digit1, space0},
        combinator::{repeat, separated},
        token::one_of,
        PResult, Parser,
    },
};

pub fn parse_usize(str: &mut &str) -> PResult<usize> {
    let a: u64 = dec_uint.parse_next(str)?;
    Ok(a as usize)
}

pub fn parse_isize(str: &mut &str) -> PResult<isize> {
    let a: i64 = dec_int.parse_next(str)?;
    Ok(a as isize)
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
        separated(
            1..,
            parse_usize,
            repeat(1.., one_of(delimiters)).fold(|| (), |_, _| ()),
        )
        .parse_next(s)
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
*/

/// parse a line like '312'
/// ```
/// use adventofcode::{framework::ParseError, line_parser};
/// assert_eq!(line_parser::to_isize("-0189"), Ok(-189));
/// assert_eq!(line_parser::to_isize("0"), Ok(0));
/// assert_eq!(line_parser::to_isize("448"), Ok(448));
/// ```
pub fn to_usize(line: &str) -> Result<usize, ParseError> {
    let s = line.to_string();
    let p = &mut s.as_str();
    Ok(parse_usize(p)?)
}

/// parse a line like '-312'
/// ```
/// use adventofcode::{framework::ParseError, line_parser};
/// assert_eq!(line_parser::to_isize("-0189"), Ok(-0189));
/// assert_eq!(line_parser::to_isize("0"), Ok(0));
/// assert_eq!(line_parser::to_isize("448"), Ok(448));
/// ```
pub fn to_isize(line: &str) -> Result<isize, ParseError> {
    let s = line.to_string();
    let p = &mut s.as_str();
    Ok(parse_isize(p)?)
}

/// parse a line like '0,-1,2,-3,40' (delimiters == &[',']) after trimming it
/// ```
/// use adventofcode::{framework::ParseError, parser};
/// assert_eq!(parser::to_isizes("0,-1,8,-9", &[',']), Ok(vec![0, -1, 8, -9]));
/// assert_eq!(parser::to_isizes("-100 200", &[' ']), Ok(vec![-100, 200]));
/// assert_eq!(parser::to_isizes("-100  200  -1", &[' ']), Ok(vec![-100, 200, -1]));
/// assert_eq!(parser::to_isizes("-100, 200  -1", &[' ', ',']), Ok(vec![-100, 200, -1]));
/// assert_eq!(parser::to_isizes("", &[',']), Err(ParseError));
/// ```
pub fn to_isizes(line: &str, delimiters: &[char]) -> Result<Vec<isize>, ParseError> {
    fn parse(s: &mut &str, delimiters: &[char]) -> PResult<Vec<isize>> {
        let _ = space0.parse_next(s)?;
        separated(
            1..,
            parse_isize,
            repeat(1.., one_of(delimiters)).fold(|| (), |_, _| ()),
        )
        .parse_next(s)
    }
    let s = line.to_string();
    let p = &mut s.as_str();
    Ok(parse(p, delimiters)?)
}

// pub fn to_isizes(line: &str, delimiter: char) -> Result<Vec<isize>, ParseError> {
//     let result = match delimiter {
//         '\n' => line
//             .trim()
//             .split(&[' ', '\t'])
//             .filter(|s| !s.is_empty())
//             .map(|n| n.parse::<isize>().expect("An invalid input as isize"))
//             .collect::<Vec<_>>(),
//         '\t' => line
//             .trim()
//             .split(&[' ', '\t', ','])
//             .filter(|s| !s.is_empty())
//             .map(|n| n.parse::<isize>().expect("An invalid input as isize"))
//             .collect::<Vec<_>>(),
//         _ => line
//             .trim()
//             .split(delimiter)
//             .filter(|s| !s.is_empty())
//             .map(|n| n.parse::<isize>().expect("An invalid input as isize"))
//             .collect::<Vec<_>>(),
//     };
//     if result.is_empty() {
//         Err(ParseError)
//     } else {
//         Ok(result)
//     }
// }

/*
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
*/

/// parse a line like '01234' after trimming it
/// ```
/// use adventofcode::{framework::ParseError, line_parser};
/// assert_eq!(line_parser::to_digits("0189"), Ok(vec![0, 1, 8, 9]));
/// assert_eq!(line_parser::to_digits("0"), Ok(vec![0]));
/// assert_eq!(line_parser::to_digits(""), Err(ParseError));
/// ```
pub fn to_digits(line: &str) -> Result<Vec<usize>, ParseError> {
    fn parse(s: &mut &str) -> PResult<Vec<usize>> {
        let n = digit1.parse_next(s)?;
        Ok(n.chars()
            .map(|n| (n as u8 - b'0') as usize)
            .collect::<Vec<_>>())
    }
    let s = line.to_string();
    let p = &mut s.as_str();
    Ok(parse(p)?)
}

/// parse a line like '010101010' after trimming it
/// ```
/// use adventofcode::{framework::ParseError, line_parser};
/// assert_eq!(line_parser::to_binaries("0"), Ok(vec![false]));
/// assert_eq!(line_parser::to_binaries("0011"), Ok(vec![false, false, true, true]));
/// assert_eq!(line_parser::to_binaries(""), Err(ParseError));
/// ```
pub fn to_binaries(line: &str) -> Result<Vec<bool>, ParseError> {
    fn parse(s: &mut &str) -> PResult<Vec<bool>> {
        let v: Vec<char> = repeat(1.., one_of(&['0', '1'])).parse_next(s)?;
        Ok(v.iter().map(|b| *b == '1').collect::<Vec<_>>())
    }
    let s = line.to_string();
    let p = &mut s.as_str();
    Ok(parse(p)?)
}

/*
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
