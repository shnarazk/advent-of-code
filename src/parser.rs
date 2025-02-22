//! misc implementations of string-to-object parsers
use {
    crate::framework::*,
    winnow::{
        ModalResult, Parser,
        ascii::{dec_int, dec_uint, digit1, space0},
        combinator::{repeat, separated},
        stream::Range,
        token::one_of,
    },
};

pub fn parse_dec(s: &mut &str) -> ModalResult<usize> {
    one_of(&['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'])
        .map(|c| (c as u8 - b'0') as usize)
        .parse_next(s)
}

pub fn parse_usize(str: &mut &str) -> ModalResult<usize> {
    dec_uint::<&str, usize, _>.parse_next(str)
}

pub fn parse_isize(str: &mut &str) -> ModalResult<isize> {
    dec_int::<&str, isize, _>.parse_next(str)
}

pub fn parse_ndigits(
    occurrences: impl Into<Range> + Copy,
) -> impl FnMut(&mut &str) -> ModalResult<usize> {
    move |input: &mut &str| {
        repeat(occurrences, one_of(|c: char| c.is_ascii_digit()))
            .map(|chars: Vec<char>| {
                chars
                    .into_iter()
                    .collect::<String>()
                    .parse::<usize>()
                    .unwrap()
            })
            .parse_next(input)
    }
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
    fn parse(s: &mut &str, delimiters: &[char]) -> ModalResult<Vec<usize>> {
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

/// parse a line like '312'
/// ```
/// use adventofcode::{framework::ParseError, parser};
/// assert_eq!(parser::to_usize("-189"), Err(ParseError));
/// assert_eq!(parser::to_usize("0"), Ok(0));
/// assert_eq!(parser::to_usize("448"), Ok(448));
/// ```
pub fn to_usize(line: &str) -> Result<usize, ParseError> {
    let s = line.to_string();
    let p = &mut s.as_str();
    Ok(parse_usize(p)?)
}

/// parse a line like '-312'
/// ```
/// use adventofcode::{framework::ParseError, parser};
/// assert_eq!(parser::to_isize("-189"), Ok(-189));
/// assert_eq!(parser::to_isize("0"), Ok(0));
/// assert_eq!(parser::to_isize("448"), Ok(448));
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
    fn parse(s: &mut &str, delimiters: &[char]) -> ModalResult<Vec<isize>> {
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

/// parse a line like '01234' after trimming it
/// ```
/// use adventofcode::{framework::ParseError, parser};
/// assert_eq!(parser::to_digits("0189"), Ok(vec![0, 1, 8, 9]));
/// assert_eq!(parser::to_digits("0"), Ok(vec![0]));
/// assert_eq!(parser::to_digits(""), Err(ParseError));
/// ```
pub fn to_digits(line: &str) -> Result<Vec<usize>, ParseError> {
    fn parse(s: &mut &str) -> ModalResult<Vec<usize>> {
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
/// use adventofcode::{framework::ParseError, parser};
/// assert_eq!(parser::to_binaries("0"), Ok(vec![false]));
/// assert_eq!(parser::to_binaries("0011"), Ok(vec![false, false, true, true]));
/// assert_eq!(parser::to_binaries(""), Err(ParseError));
/// ```
pub fn to_binaries(line: &str) -> Result<Vec<bool>, ParseError> {
    fn parse(s: &mut &str) -> ModalResult<Vec<bool>> {
        let v: Vec<char> = repeat(1.., one_of(&['0', '1'])).parse_next(s)?;
        Ok(v.iter().map(|b| *b == '1').collect::<Vec<_>>())
    }
    let s = line.to_string();
    let p = &mut s.as_str();
    Ok(parse(p)?)
}
