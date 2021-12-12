use {
    crate::framework::ParseError,
    lazy_static::lazy_static,
    regex::Regex,
};

/// parse a line like '0,1,2,3,4' (delimiter == ',') after trimming it
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

/// parse a line like '01234' after trimming it
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
            _ => panic!(),
        })
        .collect::<Vec<usize>>();
    if result.is_empty() {
        Err(ParseError)
    } else {
        Ok(result)
    }
}

/// parse a line like '010101010' after trimming it
pub fn to_binaries(line: &str) -> Result<Vec<bool>, ParseError> {
    lazy_static! {
        static ref PARSER: Regex = Regex::new(r"^[01]+$").expect("wrong");
    }
    let segment = PARSER.captures(line.trim()).ok_or(ParseError)?;
    Ok(segment[0].chars().map(|s| s == '1').collect::<Vec<bool>>())
}

/// parse a line like 'ewnswss' after trimming it
pub fn to_chars(line: &str) -> Result<Vec<char>, ParseError> {
    Ok(line.trim().chars().collect::<Vec<_>>())
}
